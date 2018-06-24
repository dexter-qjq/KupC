#include <stdio.h>
int lightNS = 1;
int lightEW = 3;

int global1 = 2 ;
int global2 = 2 ;
int y = 100 ;
int changeNS(){
	switch (lightNS) {
		case(1):
			lightNS = 2;
			return 0;
		case(2):
			lightNS = 3;
			return 0;
		case(3):
			if (lightEW == 3 ) {
				lightNS = 1;
			}
			return 0;
	}
}
int changeEW(){
	switch (lightEW) {
		case(1):
			lightEW = 2;
			return 0;
		case(2):
			lightEW = 3;
			return 0;
		case(3):
			if (lightNS == 3 ) {
				lightEW = 1;
			}
			return 0;
	}
}

int main(void){
	int i = 5 ;
	int x ;
		while(i >= 0) {
		inupdatepoint ;
		updatepoint;
		changeEW() + changeNS();
	 	i = i - 1 ;
		printf("NS=%d\tEW=%d\n", lightNS,lightEW) ;
		inupdatepoint;
	}
	
	return 0;
}
