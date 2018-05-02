#include "string.h"
#include "stdio.h"

struct ArcCell{
	int adj;  
}; 

struct VertexType{
	int number;    
	char *city;   
}; 

struct MGraph{
	struct VertexType vex[5];  
	struct ArcCell arcs[5][5]; 
	int vexnum;  
}; 

struct student 
{	
	int name ;
	int code ;
};

struct student gcl ;


struct MGraph G; 

int P[5][5];
long int D[5];

void CreateUDN()  
{ 	int i,j;
	gcl.name = 10 ;
	gcl.code = 20 ;
	for(i=0;i<5;++i) G.vex[i].number=i;
	G.vex[0].city="aaa";
	G.vex[1].city="bbb";
	G.vex[2].city="ccc";
	G.vex[3].city="ddd";
	G.vex[4].city="eee";
	for(i=0;i<5;++i)
		for(j=0;j<5;++j)
			G.arcs[i][j].adj=20000;
	G.arcs[0][2].adj=G.arcs[2][0].adj=1892;
	G.arcs[1][2].adj=G.arcs[2][1].adj=216;
	G.arcs[2][3].adj=G.arcs[3][2].adj=1145;	
	G.arcs[3][4].adj=G.arcs[4][3].adj=668;
}

void narrate() 
{
	int i,k=0;
	printf("\nthe city list is shown below:\n\n");
	for(i=0;i<5;i++)
	{
		printf("(%4d)%8s",i,G.vex[i].city); 
		k=k+1;
		if(k%5==0) printf("\n");
	}
}

void welcome()
{
	printf("welcome to travel map !\n");
	narrate();
}


void ShortestPath( int num ) 
{
	inupdatepoint ;
	CreateUDN();
	updatepoint;
	welcome();
	updatepoint;
	int v,w,i,t;
	int final[5];
	int min;
	for(v=0;v<5;++v)
	{
		final[v]=0;
        D[v]=G.arcs[num][v].adj;
		for(w=0;w<5;++w)
        P[v][w]=0;
		if(D[v]<20000) {
        P[v][num]=1;
		P[v][v]=1;}
	}
	D[num]=0;
	final[num]=1;
	for(i=0;i<5;++i)
	{
		min=20000;
		for(w=0;w<5;++w)
			if(!final[w])
				if(D[w]<min){v=w;min=D[w];}
		final[v]=1;
		for(w=0;w<5;++w)
		{	
			if(!final[w]&&((min+G.arcs[v][w].adj)<D[w]))
			{	
				D[w]=min+G.arcs[v][w].adj;
				for(t=0;t<5;t++) P[w][t]=P[v][t];
				P[w][w]=1;
			}
		}
	}
	inupdatepoint ;	
}



void output(int city1, int city2) 
{
	int a,b,c,d,q=0;
	a=city2;
	if(a!=city1)
	{
		printf("\nfrom %s to %s the best path is ",G.vex[city1].city,G.vex[city2].city);
		printf("(the shortest distance is %ldkm.)\n\t",D[a]);
		printf("%s",G.vex[city1].city);
		d=city1;
		for(c=0;c<5;++c)
		{
gate:; 
	 P[a][city1]=0;
	 for(b=0;b<5;b++)
	 {
		 if(G.arcs[d][b].adj<20000 && P[a][b])
		 {
			 printf(" --> %s ",G.vex[b].city);q=q+1;
			 P[a][b]=0;
			 d=b;
			 if(q%8==0) printf("\n");
			 goto gate;
		 }
	 }
		}
	}

}

void shuchu()
{
	printf("%d\n",gcl.name);
}

int main() 
{
	inupdatepoint;
	int v0,v1;
	v0 = 0 ; v1 = 1 ;
	ShortestPath(v0);
	updatepoint ;
        output(v0,v1);
	printf("\n\n\n");
	inupdatepoint ;
	inupdatepoint ;
	ShortestPath(v0);
	updatepoint ;	
        output(v0,v1);
	printf("\n\n\n");
	inupdatepoint ;
	shuchu();
   	return 0;
}
