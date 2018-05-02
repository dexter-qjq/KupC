itisupdatepatch;

extern int global1 ;
extern int global2 ;
extern int lightEW ;
extern int lightNS ;

int changeNS_New(){
	switch (lightNS) {
		case(1):
			lightNS = 2;
			return 1;
		case(2):
			lightNS = 3;
			return 1;
		case(3):
			global1 = global1 - 1 ;
			if (lightEW == 3 && global1 >= 1) {
				lightNS = 1;
				global2 = 4 ;
			}
			return 1;
	}
}
int changeEW_New(){
	switch (lightEW) {
		case(1):
			lightEW = 2;
			return 1;
		case(2):
			lightEW = 3;
			return 1;
		case(3):
			global2 = global2 - 1 ;
			if (lightNS == 3 && global2 >= 1) {
				lightEW = 1;
				global1 = 4 ;
			}
			return 1;
	}
}

hereisend;
