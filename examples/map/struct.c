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

