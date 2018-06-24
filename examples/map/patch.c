#include <stdio.h>
#include "struct.c"

itisupdatepatch ;

extern struct MGraph G;

void CreateUDN_New() 
{ int i,j;
	for(i=0;i<7;++i) G.vex[i].number=i;
	G.vex[0].city="v0";
	G.vex[1].city="v1";
	G.vex[2].city="v2";
	G.vex[3].city="v3";
	G.vex[4].city="v4";
	G.vex[5].city="v5";
	G.vex[6].city="v6";
	for(i=0;i<5;++i)
		for(j=0;j<5;++j)
			G.arcs[i][j].adj=20000;
	G.arcs[0][1].adj=G.arcs[1][0].adj=1;
	G.arcs[0][2].adj=G.arcs[2][0].adj=2;
	G.arcs[0][3].adj=G.arcs[3][0].adj=3;	
	G.arcs[1][4].adj=G.arcs[4][1].adj=2;
	G.arcs[1][5].adj=G.arcs[5][1].adj=3;
	G.arcs[4][6].adj=G.arcs[6][4].adj=3;
	G.arcs[3][6].adj=G.arcs[6][3].adj=2;
	G.arcs[2][5].adj=G.arcs[5][2].adj=2;
	G.arcs[6][5].adj=G.arcs[5][6].adj=2;
}

hereisend ;
