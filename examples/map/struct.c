struct ArcCell{
	int adj;
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

