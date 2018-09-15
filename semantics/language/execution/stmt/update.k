module C-STMT-UPDATE
     imports C-BINDING-SYNTAX
     imports C-BUILTIN-SYNTAX
     imports C-CHECK-LOC-SYNTAX
     imports C-DECL-INITIALIZER-SYNTAX
     imports C-DYNAMIC-SYNTAX
     imports C-ENV-SYNTAX
     imports C-ERROR-SYNTAX
     imports C-MEMORY-ALLOC-SYNTAX
     imports C-SEQUENCE-POINT-SYNTAX
     imports C-SYMLOC-SYNTAX   
     imports C-SYNTAX
     imports C-TYPING-COMPATIBILITY-SYNTAX
     imports C-TYPING-SYNTAX
     imports C-TYPING-CANONICALIZATION
     imports C-BITS-SYNTAX
     imports C-COMMON-EXPR-MEMBERS 

     imports COMPAT-SYNTAX 
     imports C-UPDATE
     imports C-STMT-UPDATE

	syntax K ::= "check-updatepoint" "(" CId ")"
		   | "do-update" | "check-struct-version'" "(" CId "," Int "," K ")"
		   | "check-struct-update" "(" CId "," CId ")"
		   | "do-struct-update" "(" CId "," CId ")"
		   | "nclv'" "(" K "," Type ")"
		   | "save-struct-data" "("  CId ")" 
		   | "save-struct-data'" "(" K "," Map "," Map ")"
		   | "save-struct-data''" "(" K "," CId "," Int "," K ")"
		   | "("CId "::" Type ")"    
		   | "data-transform" "(" K ")" 
		   | "data-transform'" "(" K "," Map "," Map ")"
		   | "do-transform" "(" K "," CId "," Int ")"
		   | "clear-mem" "(" K "," Int "," K ")" | "reval''" "(" K ")"
		   | "do-update'" "(" CId ","CId ")" 
		   | "do-update''" "(" CId "," CId ")"
		   | "patch-available" "(" CabsLoc ")"
		   | "check-capability" "(" CabsLoc "," Set ")"
		   | "check-contextual-first" "(" CabsLoc "," Set ")"
		   | "check-contextual-second" "(" CabsLoc "," Set ")"
		   | "(" Set "," Set "," Set ")" | "begin-end""(" Int "," Int ")"
		   | "point-pair" "(" K "," K ")"
		   | "whether-do-update"
		   | "update-function" "(" K "," K ")"
		   | "for-checking"

	context Call(HOLE => reval'(HOLE),_)  [ndheat]

	
/* do struct update    check-struct-version => . ... </k>         */
	rule <k> (check-struct-version(X:CId,_,Base:K) ~> nclv(Loc:SymLoc, T:Type) . F:CId ) 
			=> check-struct-version'(X,I,Base) ~> nclv'(Loc, T) . Identifier("udata") . Identifier("data"). F:CId ... </k>
	     <tu> ...
		<tu-id> Patch:String </tu-id>
		<patch-tu> SetItem(Patch)  </patch-tu>
		<version> I:Int </version>
	     ... </tu>
	     <signal-for-change-struct> false => true </signal-for-change-struct>
	when  (F =/=K Identifier("version"))      

	rule <k> (check-struct-version(_,_,_) ~> nclv(Loc:SymLoc, T:Type) . F:CId ) 
			=> nclv(Loc, T) . Identifier("udata") . Identifier("data"). F:CId ... </k>
	     <patch-unit> .Set </patch-unit>

	rule <k> (check-struct-version(_,_,_) ~> nclv(Loc:SymLoc, T:Type) . F:CId ) => nclv(Loc:SymLoc, T:Type) . F:CId ... </k>
	when F ==K Identifier("version")

	rule <k> nclv'(Loc:SymLoc, t(Q:Set,structType(F:CId,I:Int, _:FieldInfo))) => nclv(Loc,t(Q,structType(F,I,Fields)))  ... </k>
	     <signal-for-change-struct> true => false  </signal-for-change-struct>
	     <signal-for-update-finish> true  </signal-for-update-finish>
	     <tu> ...
		<tu-id> Patch:String </tu-id>
		<patch-tu> SetItem(Patch) </patch-tu>
	        <gstructs> ... 
			F |-> Fields:FieldInfo
		...</gstructs>
	     ... </tu>

	rule <k> nclv'(Loc:SymLoc, T:Type) => nclv(Loc,T) ... </k>
	     <signal-for-change-struct> true => false  </signal-for-change-struct>
	     <signal-for-update-finish> false </signal-for-update-finish>


	rule <k> nclv'(Loc:SymLoc, t(Q:Set,structType(F:CId,I:Int, Fields:FieldInfo))) => nclv(Loc,t(Q,structType(F,I,Fields))) ... </k>
	     <signal-for-change-struct> true => false  </signal-for-change-struct>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted-struct> Q1:Set </wanted-struct>
	 when notBool (F in Q1)

// it is the newest
// check-struct-version'(struct name, version, struct variable name)
//check whether it is the newest version
	// update not happen
	rule <k> check-struct-version'(_,_,_) => . ... </k>
	     <signal-for-update-finish> false  </signal-for-update-finish>

	// it is the newest version, so do nothing   and  the occurrance of the update 
//	rule <k> check-struct-version'(_ , I1:Int , Base:K) => . ...</k> 
//	     <signal-for-update-finish> true  </signal-for-update-finish>
//	     <mem> ... 
//			Base |-> object(_,_,_:Int |-> piece ( I2:Int , _ )_ )
//	     ... </mem>
//	     when I2 ==Int I1 
	
	// it is not the newest version , then update the version information and check whether the struct need to be updated  
	rule <k> check-struct-version'(X:CId, I1:Int , Base:K) => 
		#if Y.Identifier("version") ==K tv(I1,t(.Set,int))  
		#then  .K 
		#else Computation(Y.Identifier("version") := tv(I1,t(.Set,int))) ~> check-struct-update(X,Y) #fi
		... </k> 
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <signal-for-update-finish>  true  </signal-for-update-finish>
	     <tu-id> MainTu </tu-id>
	     <genv> ... 
			Y:CId |-> Base 
	     ... </genv>


	rule <k> check-struct-version' (_,I:Int,Base:K) => . ... </k>
		 <main-tu> SetItem(MainTu:String) </main-tu>
	     <signal-for-update-finish>  true  </signal-for-update-finish>
	     <tu-id> MainTu </tu-id>
	     <genv> Rho:Map </genv>
		 <mem> ...
			Base |-> object(_,_, 0|-> piece(_ => I,_ )_)
	 	 ... </mem>
			when notBool(Base in values(Rho))



//	     <mem> ... 
//			Base |-> object(_,_,_:Int |-> piece ( I2:Int , _ )_ )
//	     ... </mem>
//	     when I2 =/=Int I1 

	// struct that do not need update 
	rule <k> check-struct-update(X:CId,_) => . ... </k>
	     <tu-id> Patch:String </tu-id>	
	     <patch-tu> SetItem(Patch) </patch-tu>	
	     <wanted-struct> Q:Set </wanted-struct>
	     when notBool (X in Q)
		
	// struct that need update 
	rule <k> check-struct-update(X:CId,Y:CId) => save-struct-data(Y) ~> do-struct-update( X , Y ) ... </k>
	     <tu-id> Patch:String </tu-id>	
	     <patch-tu> SetItem(Patch) </patch-tu>	
	     <wanted-struct> Q:Set </wanted-struct>
	     when  (X in Q)

	// save struct data  
	rule <k> save-struct-data(Y:CId) => save-struct-data'(Base,Rho1,Rho2) ... </k>
	     <genv> ... Y |-> Base:K ... </genv>
	     <mem> ...
		   Base |-> object(t(_,structType(_,_,fieldInfo(_,
			_ Identifier ( "udata" ) |-> t ( _, unionType ( _ , _, fieldInfo ( _, Identifier ( "data" ) |-> t ( _ , structType ( _ , _ , fieldInfo ( _, Rho1:Map , Rho2:Map ))) _ , _ )))_,_))),_,_)
	     ... </mem> 

	rule <k> (.K => save-struct-data''(Base, X, I +Int 4 ,sizeofType(T))) ~> save-struct-data'(Base:K,(X:CId |-> T:Type => .Map)_,(X:CId|-> I:Int => .Map)_) ... </k>
	     <saved-struct-data> ... .Map => (X::T) |-> list(.List) </saved-struct-data>
	
	context  save-struct-data''(_,_,_,HOLE:K)

	rule <k> save-struct-data''( Base:K , X:CId , I:Int  => I +Int 1 , tv(I1:Int => I1 -Int 1 ,_)) ... </k>
	     <saved-struct-data> ... (X::_) |-> list(_ (.List => ListItem(P))) ... </saved-struct-data>
	     <mem> ... 
		Base |-> object(_,_,_ I |-> P:K _) 
	     ... </mem>


	rule <k> save-struct-data''( Base:K , _, I:Int  => I +Int 1 , tv(I1:Int => I1 -Int 1 ,_)) ... </k>
	    // <saved-struct-data> ... (X::_) |-> list(_ (.List => ListItem(P))) ... </saved-struct-data>
	    <mem> ... 
		Base |-> object(_,_,Rho:Map) 
	     ... </mem>
	when notBool( I in keys(Rho)) 

	rule <k> save-struct-data''(_,_,_,tv(0,_)) => . ...</k>	 
	rule <k> save-struct-data'(_,.Map,.Map) => . ... </k>    

	rule <k>  do-struct-update(X:CId,Y:CId) => data-transform(Base) ... </k> 
	     <tu> ...
		<tu-id> Patch:String </tu-id>
		<patch-tu> SetItem(Patch) </patch-tu>
	        <gstructs> ... 
			X |-> Fields:FieldInfo
		...</gstructs>
	     ... </tu>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ... 
		<tu-id> MainTu </tu-id>
	        <gtypes> ...
			Y |->  t ( _ , structType ( X , _ , (_ => Fields)))
		... </gtypes>
		<genv> ...
			Y |-> Base:K
		... </genv>
	     ... </tu>
	     <mem> ...
		Base |-> object(t ( _ , structType ( X , _ , (_ => Fields))),_,_)
	     ... </mem>
	     <external-types> ... 
		Y |->  t ( _ , structType ( X , _ , (_ => Fields)))
	     ... </external-types>    

	rule <k> data-transform(Base:K) => data-transform'(Base,Rho1,Rho2)... </k>
	     <mem> ...
		Base |-> object(t( _ , structType ( Identifier(S:String) , _ , _)) ,_,_)
	     ... </mem>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <gstructs> ... 
			Identifier(S2:String) |-> fieldInfo(_,Rho1:Map,Rho2:Map)
	     ... </gstructs>
	     when S2 ==K (S +String "_old") 

	rule <k> (.K => do-transform(Base,X,I +Int 4)) ~> data-transform'(Base:K,(X:CId |-> T:Type => .Map)_ , (X |-> I:Int => .Map)_) ... </k>
	     <saved-struct-data> Rho:Map </saved-struct-data>
	when (X::T) in keys(Rho)

	rule <k> (.K => clear-mem(Base,I +Int 4,sizeofType(T))) ~> data-transform'(Base:K,(X:CId |-> T:Type => .Map)_ , (X |-> I:Int => .Map)_) ... </k>
	     <saved-struct-data> Rho:Map </saved-struct-data>
	when notBool ((X::T) in keys(Rho))

	context clear-mem(_,_,HOLE:K)

	rule <k> do-transform(Base:K,X:CId, I:Int => I +Int 1) ... </k>
	     <saved-struct-data> ... 	
		 	(X :: _) |-> list((ListItem(P:K) => .List)_)
	     ... </saved-struct-data>
	     <mem> ... 
		Base |-> object(_,_,_ I |-> (_ => P) _) 
	     ... </mem>               

	rule <k> do-transform(_,X:CId,_) => . ... </k>
	     <saved-struct-data> ... 
			(X :: _) |-> list(.List)
	     ... </saved-struct-data> 		
	
	rule <k> clear-mem(Base:K, I:Int => I +Int 1,tv(I1:Int => I1 -Int 1,_)) ... </k>
	     <mem> ... 
			Base |-> object(_,_,_ I |-> (_ => piece(unknown,8)))
	     ... </mem>
	     when I1 >Int 0 		 
	
	rule <k> clear-mem(_,_,tv(0,_)) => . ... </k>

	rule <k> data-transform'(_,.Map,.Map) => . ... </k>
	     <saved-struct-data> _ => .Map </saved-struct-data>

// update safety check 
	rule <k> Inupdatepoint => . ... </k> 
	
	rule <k> Updatepoint => Inducedpoint ... </k>


// 1. check whether the patch is available 
	rule <k> Inducedpoint => patch-available(Loc) ... </k>
	     <curr-program-loc> Loc:K </curr-program-loc>
	     <signal-for-update-finish> false </signal-for-update-finish>	
		
	rule <k>  Inducedpoint => . ... </k>
	     <signal-for-update-finish> true </signal-for-update-finish>

	rule <k> patch-available(Loc:K) => check-capability(Loc,Q) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>			

	rule <k> patch-available(_) => . ... </k>
	     <patch-unit> .Set </patch-unit>

// 2. check the capability of the update point to hold the type safety 
	rule <k> check-capability(_,(SetItem((_,_)) => .Set)_)  ... </k>

	rule <k> check-capability(Loc:K,(SetItem(Identifier(S1:String)) => .Set)_)  ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <patch-unit> SetItem(Patch:String) </patch-unit>
	     <tu> ... 
	     <tu-id> Patch </tu-id>
	     <gtypes> ... Identifier(S1) |-> T:Type ...</gtypes>
	     ... </tu>
	     <tu> ...
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,Q:Set,_) ... </induced-points>
	     <original-func> ... SetItem(Identifier(S2:String)) ... </original-func>
	     <gtypes> ... Identifier(S2) |-> T ... </gtypes>
	     ...</tu>
	 when (S1 ==K (S2 +String "_New")) andBool  (Identifier(S2) in Q)	

	rule <k> check-capability(Loc:K,SetItem(Identifier(S1:String)) _) => . ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <patch-unit> SetItem(Patch:String) </patch-unit>
	     <tu> ... 
	     <tu-id> Patch </tu-id>
	     <gtypes> ... Identifier(S1) |-> T1:Type ...</gtypes>
	     ... </tu>
	     <tu> ...
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,Q:Set,_) ... </induced-points>
	     <original-func> ... SetItem(Identifier(S2:String)) ... </original-func>
	     <gtypes> ... Identifier(S2) |-> T2:Type ... </gtypes>
	     ...</tu>
	 when (S1 ==K (S2 +String "_New")) andBool (Identifier(S2) in Q) andBool (T1 =/=K T2)	

	rule <k> check-capability(_, (SetItem(Identifier(S:String)) => .Set)_) ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu-id> MainTu </tu-id>
	     <original-func> Q:Set </original-func>  
	     when notBool(Identifier(S) in Q)       [owise]

 	rule <k> check-capability(Loc:K,(SetItem(Identifier(S1:String))=> .Set) _) ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,Q:Set,_) ... </induced-points>
	     <original-func> ... SetItem(Identifier(S2:String)) ... </original-func>
	 when (S1 ==K (S2 +String "_New")) andBool (notBool (Identifier(S2) in Q))	

	rule <k> check-capability(Loc:K,(SetItem((X:CId,"struct")) => .Set)_) ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,Q:Set,_) ... </induced-points>    	
	 when  notBool (X in Q)		

	rule <k> check-capability(Loc:K,SetItem((X:CId,"struct"))_) => . ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,Q:Set,_) ... </induced-points>    	
	 when  (X in Q)		

	rule <k> check-capability(Loc:K,.Set) => check-contextual-first(Loc,Q1) ... </k>
             <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (Q1:Set , _, _) ... </induced-points>


// 3. check the perior effect of the update point 
	rule <k> check-contextual-first(_,(SetItem(X:CId) => .Set)_) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	     <gstructs> Rho:Map </gstructs>
	 when notBool( (X , "struct") in Q) andBool (X in keys(Rho))   
	     
	rule <k> check-contextual-first(Loc:K,SetItem(X:CId)_) => check-contextual-second(Loc,Q2) ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ...
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	     <gstructs> Rho:Map </gstructs>
	     ... </tu>
	     <tu> ...
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,_,Q2:Set) ... </induced-points>
	     ... </tu>
	 when (X , "struct") in Q andBool (X in keys(Rho))   

	rule <k> check-contextual-first(_,(SetItem(Identifier(S:String)) => .Set)_) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	 when notBool( Identifier(S +String "_New") in Q)   

        rule <k> check-contextual-first(Loc:K,SetItem(Identifier(S:String))_) => check-contextual-second(Loc,Q2) ... </k>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ...
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	     ... </tu>
	     <tu> ...
	     <tu-id> MainTu </tu-id>
	     <induced-points> ... Loc |-> (_,_,Q2:Set) ... </induced-points>
	     ... </tu>
	 when Identifier(S +String "_New") in Q   

// 4. check the future effect of update point
	rule <k> check-contextual-second(_,(SetItem(X:CId) => .Set)_) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	     <gstructs> Rho:Map </gstructs>
	 when notBool( (X , "struct") in Q) andBool (X in keys(Rho))   
	     
	rule <k> check-contextual-second(_,SetItem(X:CId)_) => . ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	     <gstructs> Rho:Map </gstructs>
	 when (X , "struct") in Q andBool (X in keys(Rho))   

	rule <k> check-contextual-second(_,(SetItem(Identifier(S:String)) => .Set)_) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	 when notBool( Identifier(S +String "_New") in Q)  

        rule <k> check-contextual-second(_,SetItem(Identifier(S:String))_) => . ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> Q:Set </wanted>
	 when Identifier(S +String "_New") in Q 

// 5. If the version consistency is holden, ready to update ....  
	rule <k> check-contextual-first(_,.Set) => whether-do-update ... </k> 
	rule <k> check-contextual-second(_,.Set) => whether-do-update ... </k>   

// non-determinism 
	rule <k> whether-do-update => do-update  ... </k>
	     <update-line> _ => Loc:K </update-line>
	     <update-signal> false => true </update-signal>
	     <curr-program-loc> Loc </curr-program-loc>      [update]

	rule <k> whether-do-update => . ... </k>       	     [update]

//  i can't find where i first introduce it , so just ignore it .
	rule <k> check-updatepoint (_) => . ... </k>

// it is safe to update  
	rule <k> (.K => update-function(Loc1,Loc2)) ~> do-update ... </k>
	     <tu> ...
		<tu-id> Tu1:String </tu-id>
		<patch-tu> SetItem(Tu1) </patch-tu>
		<wanted> SetItem(X:CId) => .Set ... </wanted>
		<goto-map> ... 	
			X |-> map(Rho1:Map funLabel(X) |-> gotoObject(I:Int, L1:List, K:K, L2:List, L3:List) Rho2:Map)
		... </goto-map>
		<gtypes> ... X |-> T:Type ... </gtypes>
		<genv> ... X |-> Loc1:K ... </genv>
	     ... </tu>
	     <main-tu> SetItem(MainTu:String) </main-tu>		
	     <tu> ...
		<tu-id> MainTu </tu-id>
		<goto-map> ... 
			Identifier(R:String) |-> map((_:Map => Rho1) 
			           funLabel(Identifier(R)) |-> gotoObject((_:Int => I), (_:List => L1), (_:K => K), (_:List => L2), (_:List=>L3)) (_:Map => Rho2))
		... </goto-map>
		<gtypes> ... Identifier(R) |-> ( _ => T ) ... </gtypes>	
		<genv> ... Identifier(R) |-> Loc2:K ... </genv>
	     ... </tu>
	     <external-types> ... Identifier(R) |-> (_ => T) ... </external-types>
	when Identifier(R +String "_New") ==K X

	syntax K ::= "update-function'" "(" K "," K ")"
		   | "update-function''" "(" K "," K ")"
	rule <k> update-function(Loc1:K, Loc2:K) => ( update-function'(Func,Loc2) ~> update-function''(Obj:K,Loc2) ) ... </k>
	     <functions> ... Loc1 |-> Func:K ... </functions>
	     <mem> ... Loc1 |-> Obj:K ... </mem>
	 
	rule <k> update-function'(functionObject(_,L:List,T:Type,_), Loc:K) => . ... </k>
	     <functions> ... Loc |-> functionObject(_, (_ => L), (_ => T), _) ... </functions>
	
	rule <k> update-function''(Obj:K , Loc:K) => . ... </k>
	     <mem> ...  Loc |-> (_ => Obj) ... </mem>	

	rule <k> do-update ... </k>
	     <patch-unit> SetItem(Patch:String) </patch-unit>
	     <tu> ...
		  <tu-id> Patch </tu-id>
      		  <wanted> SetItem(X:CId) => .Set ... </wanted>
	          <goto-map> ... X |-> map(Rho:Map) ... </goto-map>
		  <gtypes> ... X |-> T:Type ... </gtypes>
	          <genv> ... X |-> Loc:K ... </genv>
	     ... </tu>
 	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ... 
		  <tu-id> MainTu </tu-id>
	          <goto-map> Rho2:Map(.Map => X |-> map(Rho)) </goto-map>
	          <genv> ... (.Map => X |-> Loc) </genv>
	          <gtypes> ... (.Map => X |-> T) </gtypes>
	     ... </tu>
	     when notBool(X in keys(Rho2)) [owise]

	rule <k> ( .K  => do-update'(Identifier(S1),F2)) ~> do-update ... </k>
	     <tu> ...
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <wanted> SetItem((Identifier(S1:String),"struct")) => .Set  ... </wanted>  
	     <gstructs> ... 
		Identifier(S1)         |-> Field1:FieldInfo
		Identifier(S2:String)  |-> Field2:FieldInfo
	     ... </gstructs>
	     ... </tu>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ...
		<tu-id> MainTu </tu-id>
		<gstructs> ...
	 	Identifier(S1) |-> ( fieldInfo(_ ListItem(typedDeclaration ( t ( _ , unionType ( F2:CId, _ , _ ) ) , _ )) _,_,_) => Field1)
		Identifier(S2) |-> ( _ => Field2)
		... </gstructs>
	      ... </tu>
	      when S2 ==K (S1 +String "_old")

	rule <k> do-update'(X:CId,F2:CId) => do-update''(F1,F2) ... </k>
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <gstructs> ... 
		X |-> fieldInfo(_ ListItem(typedDeclaration ( t ( _ , unionType ( F1:CId, _ , _ ) ) , _ )) _,_,_)
	     ... </gstructs>

	rule <k>  do-update''(F1,F2) => . ... </k>
	     <tu> ...
	     <tu-id> Patch:String </tu-id>
	     <patch-tu> SetItem(Patch) </patch-tu>
	     <gstructs> ... 
		F1:CId |-> Fields:FieldInfo
	     ... </gstructs>
	     ... </tu>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ...
		<tu-id> MainTu </tu-id>
		<gstructs> ...
	 	( F2:CId |-> _ ) => (F1 |-> Fields)
		... </gstructs>
	      ... </tu>
		
	rule <k> do-update  ... </k>
	     <patch-unit> SetItem(Patch:String) </patch-unit>
	     <tu> ... 
	     <tu-id> Patch </tu-id>
	     <wanted> ( SetItem((X:CId,"CId")) => .Set ) _ </wanted>
	     <genv> ... X |-> Loc:K ... </genv> 
	     <gtypes> ... X |-> T:Type ... </gtypes>
	     ... </tu>
             <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ... 
		  <tu-id> MainTu </tu-id>
	          <genv> ... (.Map => X |-> Loc) </genv>
	          <gtypes> ... (.Map => X |-> T) </gtypes>
	     ... </tu>
	     

	rule <k> do-update => for-checking  ... </k>
	     <signal-for-update-finish> false => true  </signal-for-update-finish>
	     <main-tu> SetItem(MainTu:String) </main-tu>
	     <tu> ...
	     <tu-id> MainTu </tu-id>
	     <version> I:Int => I +Int 1 </version>
	     ... </tu>
	     <tu> ...			
	     <tu-id> Tu:String </tu-id>
	     <patch-tu> SetItem(Tu) </patch-tu>
	     <wanted>  .Set  </wanted>
	     ... </tu>    
	rule <k> for-checking => . ... </k> [finish-update]


	rule <k> lookupField (X:CId,Loc:SymLoc,Q:Set,Y:CId,fieldInfo(_ ListItem(typedDeclaration(_,Z:CId))_,_,_) ,Fields:FieldInfo) 
		 => nclv(Loc,t(Q,structType(Y,9999,Fields))) .Identifier("udata") .Identifier("data") .X ... </k>
	when Z ==K Identifier("version") andBool (X =/=K Identifier("version")  orBool X =/=K Identifier("udata"))
endmodule 
