#ifndef __is_included__e44a1568_3e5a_11ed_ac01_b499badf00a1
#define __is_included__e44a1568_3e5a_11ed_ac01_b499badf00a1 1

#ifdef __cplusplus
	extern "C" {
#endif

#ifndef __cplusplus
	#ifndef true
		#define true 1
		#define false 0
		typedef unsigned char bool;
	#endif
#endif

void serialInit();

void handleSerialMessages();



#ifdef __cplusplus
	}
#endif


#endif /* #ifndef __is_included__e44a1568_3e5a_11ed_ac01_b499badf00a1 */
