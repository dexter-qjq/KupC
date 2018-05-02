#include <stdio.h>
#include "struct.c"

itisupdatepatch ;

extern struct MGraph G;
extern void narrate();

struct student 
{
	int sex ;
	int number ;
	int name ;
};

 extern struct student gcl ;

void CreateUDN_New() 
{ int i,j;
	gcl.name = 999 ;
	for(i=0;i<5;++i) G.vex[i].number=i;
	G.vex[0].city="aaa";
	G.vex[1].city="bbb";
	G.vex[2].city="ccc";
	G.vex[3].city="DDD";
	G.vex[4].city="eee";
	for(i=0;i<5;++i)
		for(j=0;j<5;++j)
			G.arcs[i][j].adj=20000;
	G.arcs[0][2].adj=G.arcs[2][0].adj=1892;
	G.arcs[1][2].adj=G.arcs[2][1].adj=206;
	G.arcs[2][3].adj=G.arcs[3][2].adj=1135;
	G.arcs[3][4].adj=G.arcs[4][3].adj=658;
	narrate();
}

void welcome_New()
{
	printf("\nwelcome to travel map !\n");
}


hereisend ;
