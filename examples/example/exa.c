#include <stdio.h>

struct T{
	int x ;
	int y ;
};
struct Q{
	int a;
	int b;
};
struct Q qjq = {99,100};


void f2(void (*fp)(int*), int *x)
{
	fp(x);
}

void f3(int x)
{
	// printf("%d ",x);
}

void f1(void (*fp)(int*), int *x)
{
	fp(x);
	f3(*x);
}

void pos(int *x)
{
	*x = 1 ;
}

void neg(int *x)
{
	*x = -1 ;
}

int main()
{
	struct T t = {1,2} ;
	qjq.a = 10 ;
	int *aaa ;
	aaa = &t.y;
	int n = 3;
	while (n > 0)
{
	//printf("%d   ",qjq.a);
	inupdatepoint;
	f1(pos,aaa);
	updatepoint;
	f2(neg,&t.x);
	updatepoint;
	if (t.x + t.y)
	{
		printf("%d %d ", t.x,t.y);
	}
	else 
	{
		printf("%d %d ", t.x,t.y);
	}
	n = n -1 ;
	f3(t.x);
	inupdatepoint;
	printf("\n\n");
}
	
	return 0 ;
}
