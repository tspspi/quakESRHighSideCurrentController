import serial
import threading
import time
import atexit
import json

from collections import deque

from time import sleep

class NotConnectedException(Exception):
	pass

class SerialRingBuffer:
	def __init__(self, bufferSize = 512):
		self.bufferSize = bufferSize
		self.buffer = [ None ] * bufferSize
		self.head = 0
		self.tail = 0
		self.lock = threading.Lock()

	def isAvailable(self, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		if self.head == self.tail:
			if blocking:
				self.lock.release()
			return True
		else:
			if blocking:
				self.lock.release()
			return False

	def available(self, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		res = 0
		if self.head >= self.tail:
			res = self.head - self.tail;
		else:
			res = self.bufferSize - self.tail + self.head
		if blocking:
			self.lock.release()
		return res

	def discard(self, len, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		avail = self.available(blocking = False)
		if avail < len:
			self.tail = (self.tail + avail) % self.bufferSize
		else:
			self.tail = (self.tail + len) % self.bufferSize
		if blocking:
			self.lock.release()
		return None

	def peek(self, distance, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		if distance >= self.available(blocking = False):
			if blocking:
				self.lock.release()
			return None
		else:
			res = self.buffer[(self.tail + distance) % self.bufferSize]
			if blocking:
				self.lock.release()
			return res

	def remainingCapacity(self, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		res = self.bufferSize - self.available(blocking = False)
		if blocking:
			self.lock.release()
		return res

	def capacity(self, *ignore, blocking = True):
		return self.bufferSize

	def push(self, data, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		if isinstance(data, list):
			if self.remainingCapacity(blocking = False) <  len(data):
				# Raise error ... ToDo
				if blocking:
					self.lock.release()
				return
			else:
				for c in data:
					self.push(c, blocking = False)
		else:
			if self.remainingCapacity(blocking = False) == 0:
				# Raise error ... ToDo
				if blocking:
					self.lock.release()
				return
			self.buffer[self.head] = data
			self.head = (self.head + 1) % self.bufferSize
		self.lock.release()

	def pop(self, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		ret = None
		if self.head != self.tail:
			ret = self.buffer[self.tail]
			self.tail = (self.tail + 1) % self.bufferSize
		if blocking:
			self.lock.release()
		return ret

	def read(self, len, *ignore, blocking = True):
		if blocking:
			self.lock.acquire()
		if self.available(blocking = False) < len:
			# ToDo Raise exception
			if blocking:
				self.lock.release()
			return None
		ret = [ None ] * len
		for i in range(len):
			ret[i] = self.buffer[(self.tail + i) % self.bufferSize]
		self.tail = (self.tail + len) % self.bufferSize
		if blocking:
			self.lock.release()
		return ret

class CurrentController:
	def __init__(self, portFile = None, commandRetries = 3):
		if not portFile:
			portFile = '/dev/ttyU0'
		self.bufferInput = SerialRingBuffer()

		self._commandRetries = commandRetries

		self.port = False
		self.portFile = portFile
		# 19200
		self.port = serial.Serial(portFile, baudrate=2400, bytesize=serial.EIGHTBITS, parity=serial.PARITY_NONE, stopbits=serial.STOPBITS_ONE, timeout=30)
		self.thrProcessing = threading.Thread(target=self.communicationThreadMain)
		self.thrProcessing.start()

		atexit.register(self.close)

		# Condition variable used to implement synchronous calls
		# for execution from jupyter notebook, synchronous simple scripts, etc.
		#
		# messageFilter contains the name of the message the application wants to wait for
		# messageResponse will contain the payload decoded by the communication thread after the filter has matched
		self.messageFilter = None
		self._lastcommand = None
		self.messageResponse = None
		self.messageConditionVariable = threading.Condition()

		self.cbIdentify = None
		self.cbVersion = None
		self.cbSetCurrent = None
		self.cbADC0 = None
		self.cbCurrent = None
		self.cbError = None
		self.cbOk = None

	def __enter__(self):
		return self

	def __exit__(self, exc_type, exc_value, traceback):
		atexit.unregister(self.close)
		if self.port:
			self.port.close()
			self.port = False
		if self.thrProcessing:
			self.thrProcessing.join()
			self.thrProcessing = False

	def close(self):
		atexit.unregister(self.close)
		if self.port:
			try:
				self.off(sync = True)
			except Exception:
				# Simply ignore all exceptions
				pass
			self.port.close()
			self.port = False
		if self.thrProcessing:
			self.thrProcessing.join()
			self.thrProcessing = False

	def internal__waitForMessageFilter(self, filter):
		self.messageConditionVariable.acquire()

		self.messageFilter = filter

		# Now wait till we get a response from our processing thread ...
		remainingRetries = int(self._commandRetries)
		if remainingRetries is None:
			remainingRetries = 0
		elif remainingRetries < 0:
			remainingRetries = 0

		while self.messageResponse == None:
			if not self.messageConditionVariable.wait(timeout = 10):
				print(f"Timeout while waiting for {self.messageFilter} (Retries remaining: {remainingRetries})")
				if (remainingRetries > 0) and (self._lastcommand is not None):
					# Retry command ...
					self.port.write(self._lastcommand)
					remainingRetries = remainingRetries - 1
				else:
					self.jabber(sync = False)
					self.messageFilter = None
					self.messageResponse = None
					self._lastcommand = None
					self.messageConditionVariable.release()
					return None
		# Reset message filter, copy and release response ...
		self._lastcommand = None
		self.messageFilter = None
		retval = self.messageResponse
		self.messageResponse = None

		# Release ...
		self.messageConditionVariable.release()
		return retval

	def internal__signalCondition(self, messageType, payload):
		self.messageConditionVariable.acquire()
		if messageType != self.messageFilter:
			self.messageConditionVariable.release()
			return
		self.messageResponse = payload
		self.messageConditionVariable.notify_all()
		self.messageConditionVariable.release()

	def communicationThreadMain(self):
		try:
			while True:
				c = self.port.read(1)
				self.bufferInput.push(c)

				# Check if we have a full message

				while True:
					# First a message has to be more than 4 bytes (due to sync pattern and stop pattern)
					if self.bufferInput.available() < 4:
						break

					# And we scan for the sync pattern
					if (self.bufferInput.peek(0) == b'$') and (self.bufferInput.peek(1) == b'$') and (self.bufferInput.peek(2) == b'$'):
						break

					self.bufferInput.discard(1)

				# Continue waiting for message
				if self.bufferInput.available() < 4:
					continue

				# If we see a full message we also see the terminating linefeed
				for i in range(self.bufferInput.available()):
					if self.bufferInput.peek(i) == b'\n':
						msg = self.bufferInput.read(i)
						self.communicationThreadMain_HandleMessage(msg)
						break
		except serial.serialutil.SerialException:
			# Shutting down works via this exception
			pass
		except:
			pass




	def id(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		self.port.write(b'$$$id\n')
		self._lastcommand = b'$$$id\n'
		if sync:
			return self.internal__waitForMessageFilter("id")
		else:
			return None

	def jabber(self, *ignore, sync = False):
		if self.port == False:
			raise ElectronGunNotConnected("Electron gun currently not connected")
		self.port.write(b'$$$$$$$$$$$$id\n')
		if sync:
			return self.internal__waitForMessageFilter("id")
		else:
			return None

	def communicationThreadMain_HandleMessage(self, msgb):
		# Decode message and if a callback is registered call it. Note that event
		# handlers are usually lists of functions or functions (see documentation)
		#
		# Note for synchronous commands there is a mutex that unblocks
		# when the specified message has arrived

		# Assemble string from message byte array
		# (and verify the characters are in fact legal)
		msg=''.join([x.decode('utf-8') for x in msgb])
		msg = msg[3:]
		#print(f"[DEBUG] Received {msg}")
		if msg[0:len("id:")] == "id:":
			controllerUUID = (msg[len("id:"):]).strip()

			if self.cbIdentify:
				if type(self.cbIdentify) is list:
					for f in self.cbIdentify:
						if callable(f):
							f(self, controllerUUID)
				elif callable(self.cbIdentify):
					self.cbIdentify(self, controllerUUID)
			self.internal__signalCondition("id", { 'uuid' : controllerUUID })
		elif msg[0:len("ver:")] == "ver:":
			controllerVersion = -1
			try:
				controllerVersion = int((msg[len("ver:"):]).strip())
			except:
				pass

			if self.cbVersion:
				if type(self.cbVersion) is list:
					for f in self.cbVersion:
						if callable(f):
							f(self, controllerUUID)
				elif callable(self.cbVersion):
					self.cbVersion(self, controllerVersion)
			self.internal__signalCondition("ver", { 'version' : controllerVersion })
		elif msg[0:len("seta:")] == "seta:":
			setvalue = -1
			try:
				setvalue = int(str((msg[len("seta:"):]).strip()))
			except Exception as e:
				print(e)
				pass

			if self.cbSetCurrent:
				if type(self.cbSetCurrent) is list:
					for f in self.cbSetCurrent:
						if callable(f):
							f(self, setvalue)
				elif callable(self.cbSetCurrent):
					self.cbSetCurrent(self, setvalue)
			self.internal__signalCondition("seta", { 'setCurrent' : setvalue })
		elif msg[0:len("adc0:")] == "adc0:":
			adcval = -1
			try:
				adcval = int(str((msg[len("adc0:"):]).strip()))
			except Exception as e:
				print(e)
				pass

			if self.cbADC0:
				if type(self.cbADC0) is list:
					for f in self.cbADC0:
						if callable(f):
							f(self, adcval)
				elif callable(self.cbADC0):
					self.cbADC0(self, adcval)
			self.internal__signalCondition("adc0", { 'raw' : adcval })
		elif msg[0:len("ra:")] == "ra:":
			current = -1
			try:
				current = float(str((msg[len("ra:"):]).strip()))
			except Exception as e:
				print(e)
				pass

			if self.cbCurrent:
				if type(self.cbCurrent) is list:
					for f in self.cbCurrent:
						if callable(f):
							f(self, current)
				elif callable(self.cbCurrent):
					self.cbCurrent(self, current)
			self.internal__signalCondition("ra", { 'current' : current })
		elif msg[0:len("ok")] == "ok":
			if self.cbOk:
				if type(self.cbOk) is list:
					for f in self.cbOk:
						if callable(f):
							f(self)
				elif callable(self.cbOk):
					self.cbOk(self)
			self.internal__signalCondition("ok", { })
		elif msg[0:len("err")] == "err":
			if self.cbError:
				if type(self.cbError) is list:
					for f in self.cbError:
						if callable(f):
							f(self)
				elif callable(self.cbError):
					self.cbError(self)
			self.internal__signalCondition("err", { })
		else:
			print("Unknown message {}".format(msg))

	def id(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		self.port.write(b'$$$id\n')
		self._lastcommand = b'$$$id\n'
		if sync:
			return self.internal__waitForMessageFilter("id")
		else:
			return None

	def version(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		self.port.write(b'$$$ver\n')
		self._lastcommand = b'$$$ver\n'
		if sync:
			return self.internal__waitForMessageFilter("ver")
		else:
			return None

	def setCurrent(self, value, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		if (value < 0) or (value >= 16384):
			raise ValueError(f"Value {value} is out of range")
		cmd = b'$$$seta:' + bytes(str(value), encoding="ascii") + b'\n'
		self._lastcommand = cmd
		self.port.write(cmd)
		if sync:
			return self.internal__waitForMessageFilter("seta")
		else:
			return None

	def getSetCurrent(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		cmd = b'$$$getseta\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("seta")
		else:
			return None

	def getADC0Raw(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		cmd = b'$$$getadc0\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("adc0")
		else:
			return None

	def getCurrent(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		cmd = b'$$$geta\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("ra")
		else:
			return None

	def calibrationPoint(self, measuredMilliamps, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		measuredMilliamps = int(measuredMilliamps)
		if measuredMilliamps == 0:
			cmd = b'$$$adccal0\n'
		else:
			cmd = b'$$$adccalh:' + bytes(str(measuredMilliamps), encoding='ascii') + b'\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("ok")
		else:
			return None

	def calibrationStore(self, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		cmd = b'$$$adccalstore\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("ok")
		else:
			return None

	def protectionEnable(self, enabled = True, *ignore, sync = False):
		if self.port == False:
			raise NotConnectedException("Device currently not connected")
		if enabled:
			cmd = b'$$$enableprotection\n'
		else:
			cmd = b'$$$disableprotection\n'
		self.port.write(cmd)
		self._lastcommand = cmd
		if sync:
			return self.internal__waitForMessageFilter("ok")
		else:
			return None


# Remove this later on - this is just a sequence used for rudimentary testing
if __name__ == "__main__":
	with CurrentController(portFile = "/dev/ttyU1") as cc:
		uid = cc.id(sync = True)['uuid']
		ver = cc.version(sync = True)['version']

		print(f"Connected to board {uid}, code version {ver}")

		#for i in [0, 100, 200, 300, 400, 500 ]:

		#for i in range(0, 1300, 10):
		#	#print(f"Setting current {i}")
		#	cc.setCurrent(i, sync = True)
		#	sleep(1)
		#	adc = cc.getADC0Raw(sync=True)
		#	adc = adc['raw']

		#	current = cc.getCurrent(sync = True)['current']

		#	print(f"set={i} adc={adc} current={current}")

		#	#print(f"Currently set current: {cc.getSetCurrent(sync=True)}, ADC value: {cc.getADC0Raw(sync=True)}")

		#print(cc.setCurrent(0, sync = True))
		#sleep(1)
		#print(cc.calibrationPoint(0, sync = True))
		#sleep(1)
		#print(cc.setCurrent(1000, sync = True))
		#measValue = int(input("Measured value in mA: "))
		#print(cc.calibrationPoint(measValue, sync = True))
		#sleep(1)
		#measValue = cc.getCurrent(sync = True)
		#print(f"Measured value: {measValue}")
		#sleep(1)
		#cc.setCurrent(500, sync = True)
		#sleep(1)
		#measValue = cc.getCurrent(sync = True)
		#print(f"Measured value: {measValue}")
		#cc.setCurrent(0, sync = True)
		#print(f"Storing calibration: {cc.calibrationStore(sync = True)}")

		for a in [ 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300 ]:
			cc.setCurrent(a, sync = True)
			sleep(1)
			ma = cc.getCurrent(sync = True)['current']
			print(f"Set {a/10} mA, measured {ma} mA")
			sleep(3)
		cc.setCurrent(0, sync = True)