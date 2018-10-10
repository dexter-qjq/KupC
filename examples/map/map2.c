#include "string.h"
#include "stdio.h"

struct ArcCell{
	int adj; 
//	int pay; 
}; 

struct VertexType{
	int number;    
	char *city;   
}; 

struct MGraph{
	struct VertexType vex[7];  
	struct ArcCell arcs[7][7]; 
	int vexnum;  
}; 


struct MGraph G; 

int P[7][7];
long int D[7] = {0};

void CreateUDN()  
{ 	int i,j;
	for(i=0;i<7;++i) G.vex[i].number=i;
	G.vex[0].city="v0";
	G.vex[1].city="v1";
	G.vex[2].city="v2";
	G.vex[3].city="v3";
	G.vex[4].city="v4";
	G.vex[5].city="v5";
	G.vex[6].city="v6";
	for(i=0;i<7;++i)
		for(j=0;j<7;++j)
			G.arcs[i][j].adj=20000;
	G.arcs[0][1].adj=G.arcs[1][0].adj=1;
	G.arcs[0][2].adj=G.arcs[2][0].adj=2;
	G.arcs[0][3].adj=G.arcs[3][0].adj=3;	
	G.arcs[1][4].adj=G.arcs[4][1].adj=1;
	G.arcs[1][2].adj=G.arcs[2][1].adj=2;
	G.arcs[4][6].adj=G.arcs[6][4].adj=1;
	G.arcs[3][6].adj=G.arcs[6][3].adj=2;
	G.arcs[2][5].adj=G.arcs[5][2].adj=2;
	G.arcs[6][5].adj=G.arcs[5][6].adj=2;
}



void Shortest (int num)
{
	int v,w,i,t;
	int final[7];
	int min;
	for(v=0;v<7;++v)
	{
		final[v]=0;
        D[v]=G.arcs[num][v].adj;
		for(w=0;w<7;++w)
        	P[v][w]=0;
		if(D[v]<20000) {
        	P[v][num]=1;
			P[v][v]=1;}
	}
	D[num]=0;
	final[num]=1;
	for(i=0;i<7;++i)
	{
		min=20000;
		for(w=0;w<7;++w)
			if(!final[w])
				if(D[w]<min){v=w;min=D[w];}
		final[v]=1;
		for(w=0;w<7;++w)
		{	
			if(!final[w]&&((min+G.arcs[v][w].adj)<D[w]))
			{	
				D[w]=min+G.arcs[v][w].adj;
				for(t=0;t<7;t++) P[w][t]=P[v][t];
				P[w][w]=1;
			}
		}
	}
}


void Path( int num ) 
{
	CreateUDN();
	Shortest(num);
}


void output(int city1, int city2) 
{
	int a,b,c,d,q=0;
	a=city2;
	if(a!=city1)
	{
		printf("\nshortest from %s to %s ",G.vex[city1].city,G.vex[city2].city);
		printf(" %ldkm.\n",D[a]);
		printf("%s",G.vex[city1].city);
		d=city1;
		for(c=0;c<7;++c)
		{
			 gate1:; 
			 P[a][city1]=0;
			 for(b=0;b<7;b++)
			 {
				 if(G.arcs[d][b].adj<20000 && P[a][b])
				 {
					 printf(" --> %s",G.vex[b].city);q=q+1;
					 P[a][b]=0;
					 d=b;
					 if(q%8==0) printf("\n");
				 		goto gate1;
			 	}
		 	}
		}
	}
/*
	if(a!=city1)
	{
		printf("\ncheapest from %s to %s ",G.vex[city1].city,G.vex[city2].city);
		printf(" $%ld.\n",DD[a]);
		printf("%s",G.vex[city1].city);
		d=city1;
		for(c=0;c<7;++c)
		{
			 gate2:; 
			 PP[a][city1]=0;
			 for(b=0;b<7;b++)
			 {
				 if(G.arcs[d][b].adj<20000 && PP[a][b])
				 {
					 printf(" --> %s",G.vex[b].city);q=q+1;
					 PP[a][b]=0;
					 d=b;
					 if(q%8==0) printf("\n");
				 		goto gate2;
			 	}
		 	}
		}
	}
*/
}

void calculate(int v0, int v1)
{
	inupdatepoint ;
	updatepoint ;
	CreateUDN();

	Path(v0);

	updatepoint ;

	output(v0,v1);

	updatepoint ;
	inupdatepoint ;
}



int main() 
{
	int v0 = 0;
	int v1 = 6;

	CreateUDN();
	calculate(0,6);
	printf("\n\n");
/*
	calculate(0,6);
	printf("\n\n");

	calculate(0,6);
	printf("\n\n");*/
   	return 0;
}
