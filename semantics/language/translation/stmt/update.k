module C-TRANSLATION-STMT-UPDATE-SYNTAX 
	syntax  K ::= "check-restriction" 
	       	    | "check-struct"
		    | "check-struct'" | "pre-check"
		    | "get-main-function" | "get-main-function'" | "pop-calc"
		    | "call-list-restriction" "(" CId "," List ")"
		    | "call-struct" "(" CId "," K ")"
		    | "get-L" "(" CId "," Set ")"
		    | "in" "(" Int "," Int ")" | "out" "(" Int "," Int ")"
		    | "inCId" "(" CId "," Int ")" | "outCId" "(" CId "," Int ")"
		    | "inCId'" "(" CId "," Int ")" | "outCId'" "(" CId "," Int ")"
	 	    | "gcl-love" | "(" CId "," K ")" | "get-res-struct" "(" Set ")"
		    | "call-loc" "(" CId "," K ")"
		    | "do-res-struct" "(" CId "," Set "," Map "," K "," Set ")"
	 	    | "add-res" "(" CId "," Set ")"
		    | "finish-restriction" "(" Set ")"
		    | "finish-restriction'" "(" CId "," Set ")"
		    | "semantic-point-D" "(" Map ")" 
		    | "semantic-point-D'" "(" Int "," CId "," Set "," Set ")"
		    | "number-to-id" "(" Set ")"
		    | "begin-end""(" Int "," Int ")" | "(" Int "," CId ")"
		    | "point-pair" "(" K "," K ")"
		    | "induced-point-D" "(" Set ")"
		    | "induced-point-D'""(" Int "," Int "," Int "," Set "," Set ")"
		    | "(" Set "," Set "," Set ")"
		    | "induced-contextual" "(" Set ")"
	  	    | "induced-contextual'" "(" Int "," Int "," Int "," Set "," Set ")"
		    | "check-pair"  | "get-global""(" Set ")"
		    
		    
endmodule

module C-STMT-UPDATE

	imports C-SYNTAX
	imports C-TRANSLATION-STMT-UPDATE-SYNTAX
	imports C-SYMLOC-SYNTAX
	imports COMPAT-SYNTAX
	imports C-DYNAMIC-SYNTAX
	imports C-TYPING-SYNTAX 
	imports C-LITERAL-SYNTAX
	imports C-ERROR-SYNTAX
	imports C-COMMON-EXPR-MEMBERS

	rule <k> Itisupdatepatch => . ... </k>
	     <signal-for-updatepatch> false => true </signal-for-updatepatch>
	     <patch-unit>  .Set => SetItem(Tu) </patch-unit>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <patch-tu> _ => SetItem(Tu) </patch-tu>	
	     <version> I:Int => I +Int 1 </version>	    

	rule <k> Hereisend => . ... </k>
	     <signal-for-updatepatch> true => false </signal-for-updatepatch>

	rule <k> Updatepoint => . ...</k>

	rule <k> Inupdatepoint => . ... </k>
	     <curr-program-loc> CabsLoc(S:String,I1:Int,I2:Int,I3:Int) </curr-program-loc>
     	     <tmp-update-point> .Set => SetItem(CabsLoc(S,I1,I2,I3)) </tmp-update-point>
	     <curr-tu> Tu:String </curr-tu>
	     <curr-function> F:CId </curr-function>
	     <tu-id> Tu </tu-id>
	     <semantic-points> ... (.Map => (I1, F)|-> set(.Set)) </semantic-points>
		
        rule <k> Inupdatepoint => . ... </k>
	     <curr-program-loc> Loc1:K </curr-program-loc>
	     <tmp-update-point> SetItem(Loc2:K) => .Set </tmp-update-point>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <update-point-pair> ... (.Set => SetItem(point-pair(Loc2,Loc1))) </update-point-pair>

	rule <k> Inducedpoint => . ... </k>
	     <curr-program-loc> Loc:K </curr-program-loc>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <induced-points> ... .Map => Loc |-> (.Set , .Set , .Set) </induced-points>

	rule <computation> Inupdatepoint => . ... </computation> 
	rule <computation> Inducedpoint => . ... </computation>
	
/*   stuff about check-restriction */
	
// deal with the update point one by one 
	rule <k>  check-restriction  ... </k>
	     <cap-points> ( SetItem(Identifier(S:String)) => .Set ) ... </cap-points>
	     <env> ... Identifier("main") |-> _ @ static (Tu:String)... </env> 
	     <tu-id> Tu </tu-id>
	     <cap-point> ... ( .Set => SetItem(Identifier(S)) ) </cap-point>
	     <capability> ... (.Map => Identifier(S +String "_D")  |-> set(.Set)  
					     Identifier(S +String "_D'") |-> set(.Set) 
					     Identifier(S +String "_L")  |-> set(.Set))
	     </capability>

     rule <k> check-restriction =>  check-struct ~> get-main-function...</k>
	  <cap-points>  .Set  </cap-points>   

/*  something about the restriction of struct at some update point */
     rule <k> check-struct => . ... </k>
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> .Map </struct-restriction>

     rule <k>  (.K => check-struct') ~> check-struct ... </k>
	  <tmp-struct-restriction> .Map => Rho </tmp-struct-restriction>
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> Rho:Map </struct-restriction>
	when keys(Rho) =/=Set .Set 

     rule <k>  (.K => check-struct') ~> check-struct ... </k>
	  <tmp-struct-restriction>  Rho2:Map </tmp-struct-restriction>
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> Rho:Map </struct-restriction>
	when keys(Rho) =/=Set .Set  
	    andBool  keys(Rho2) =/=Set .Set 

     rule <k> check-struct' => . ... </k>
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> (X:CId |-> _ ) => .Map  ... </struct-restriction>
	  <capability> Rho:Map </capability>
	when notBool (X in keys(Rho))

     rule <k> check-struct' => . ... </k>
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> ( X:CId |-> set(S1:Set) ) => .Map ... </struct-restriction>
	  <capability> ... X |-> set ( _ (.Set => S1)  ) ... </capability>


// replay the process and check restriction
// call-main	
    
     rule <k> get-main-function => get-main-function' ... </k> 
	  <main-tu> SetItem(Tu:String) </main-tu>
	  <res-calc> _ => S </res-calc>
	  <tu-id> Tu </tu-id>
	  <goto-map> ... Identifier("main") |-> map ( funLabel(Identifier("main")) |-> gotoObject(_,_,S:K,_,_) _) ... </goto-map>

/*******************   deal with the call order  *******************/
// the first one 	  
     rule <k> get-main-function'  ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> .List => ListItem(Num) </res-block-history> 
	  <curr-functions> .List => ListItem(Num) </curr-functions>
	  <function-block> Rho:Map ( .Map => Num |-> begin-end(0,0) ) </function-block>
	when notBool (Num in keys(Rho))

     rule <k> get-main-function'  ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> .List => ListItem(Num) </res-block-history> 
	  <curr-functions> .List => ListItem(Num) </curr-functions>
	  <function-block> Rho:Map  </function-block>
	when  (Num in keys(Rho))


// the follower & no out before
     rule <k> get-main-function' ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> (.List => ListItem(Num)) ListItem(M:Int) ...  </res-block-history>
	  <curr-functions> (.List => ListItem(Num)) _:List </curr-functions> 
	  <recent-out-block> .Set </recent-out-block>
	  <block-pair> (.Set => SetItem(in(M,Num))) ... </block-pair>
	  <function-block> Rho:Map (.Map => Num |-> begin-end(0 , 0)) </function-block> 
	when notBool (Num in keys(Rho))

     rule <k> get-main-function' ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> (.List => ListItem(Num)) ListItem(M:Int) ...  </res-block-history>
	  <curr-functions> (.List => ListItem(Num)) _:List </curr-functions> 
	  <recent-out-block> .Set </recent-out-block>
	  <block-pair> (.Set => SetItem(in(M,Num))) ... </block-pair>
	  <function-block> Rho:Map  </function-block> 
	when  (Num in keys(Rho))

// the follower & have out before
     rule <k> get-main-function' ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> (.List => ListItem(Num)) ListItem(M:Int) ...  </res-block-history>
	  <curr-functions> (.List => ListItem(Num)) _:List </curr-functions>  
	  <recent-out-block> SetItem(N:Int) </recent-out-block>
	  <block-pair> (.Set => SetItem(in(M,Num)) SetItem(out(N,Num))) ... </block-pair>
	  <function-block> Rho:Map(.Map => Num |-> begin-end(0 , 0)) </function-block> 
	when notBool (Num in keys(Rho))

     rule <k> get-main-function' ... </k>
      	  <res-calc> (Block(Num:Int,_,list(L:List))~>_~>_ ) => listToK(L) ~> pop-calc ... </res-calc>
	  <res-block-history> (.List => ListItem(Num)) ListItem(M:Int) ...  </res-block-history>
	  <curr-functions> (.List => ListItem(Num)) _:List </curr-functions>  
	  <recent-out-block> SetItem(N:Int) </recent-out-block>
	  <block-pair> (.Set => SetItem(in(M,Num)) SetItem(out(N,Num))) ... </block-pair>
	  <function-block> Rho:Map </function-block> 
	when (Num in keys(Rho))

// pop the block number   
     rule <k> get-main-function' ... </k>
	  <res-calc> pop-calc => . ... </res-calc>
	  <res-block-history> (ListItem(M:Int) => .List) ... </res-block-history>
	  <curr-functions> (ListItem(M:Int) => .List) _:List </curr-functions>
	  <past-functions> (.List => ListItem(M)) _:List </past-functions>
	  <recent-out-block> _ => SetItem(M) </recent-out-block> 
	  <tmp-program-loc> CabsLoc(_,I1:Int,_,_) </tmp-program-loc>	
	  <function-block> ... M |-> begin-end(_:Int, ( 0 => I1)) ... </function-block>

     rule <k> get-main-function' ... </k>
	  <res-calc> pop-calc => . ... </res-calc>
	  <res-block-history> (ListItem(M:Int) => .List) ... </res-block-history>
	  <curr-functions> (ListItem(M:Int) => .List) _:List </curr-functions>
	  <past-functions> (.List => ListItem(M)) _:List </past-functions>
	  <recent-out-block> _ => SetItem(M) </recent-out-block> 
	  <function-block> ... M |-> begin-end(_:Int, I2:Int) ... </function-block>
	when I2 =/=Int 0

     rule <k> get-main-function' ... </k>
 	  <res-calc> CodeLoc (K:K , CabsLoc(S:String,I1:Int,I2:Int,I3:Int)) => K ... </res-calc> 
	  <tmp-program-loc> _ => CabsLoc(S,I1,I2,I3) </tmp-program-loc>
	  <function-block> ... _:Int |-> begin-end((0 => I1) ,_:Int) </function-block>

     rule <k> get-main-function' ... </k>
 	  <res-calc> CodeLoc (K:K , Loc:K) => K ... </res-calc> 
	  <tmp-program-loc> _ => Loc </tmp-program-loc>
	  <function-block> ... _:Int |-> begin-end( I2:Int, 0) </function-block>
	 when I2 =/=Int 0
		
// for local block statement 
     rule <k> get-main-function' ... </k>
          <res-calc> BlockStatement(Block(_,_,list(L:List))) => listToK(L) ... </res-calc>  

// this is the end of main calc 
     rule <k> get-main-function' =>  gcl-love ... </k>
	  <res-calc> .K </res-calc>

/*******************   deal with the statement   *******************/
     rule <k> get-main-function' ... </k>
          <res-calc> (For(_, _, _, _, S:K) => S) ... </res-calc> 

     rule <k> get-main-function' ... </k>
	  <res-calc> (DoWhile(_, S:K) => S) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (While(_,S:K) => S) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (Switch(_,_,S:K) => S) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (Case(_, _, _, S:K) => S) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (Default(_, S:K) => S) ... </res-calc>

     rule <k> get-main-function' ... </k>
 	  <res-calc> (IfThenElse(_, S1:K, S2:K) => S1 ~> S2) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> L:KLabel(_:KList) => . ... </res-calc>
	  when false 
		orBool (L ==KLabel 'Nop)
		orBool (L ==KLabel 'Break)
		orBool (L ==KLabel 'Continue)
		orBool (L ==KLabel 'Goto)
		orBool (L ==KLabel 'CompGoto)
	        orBool (L ==KLabel 'DeclarationDefinition)	
	        orBool (L ==KLabel 'OnlyTypedef)	
	        orBool (L ==KLabel 'Typedef)
		orBool (L ==KLabel 'Label)
	
     rule <k> get-main-function' ... </k>
	  <res-calc> Return (K:K) => K ... </res-calc>

     rule <k> get-main-function'  ... </k> 
	  <res-calc> Computation(K:K) => K ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> SizeofExpression(_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> SizeofType(_,_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> Inupdatepoint => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> Inducedpoint => . ... </res-calc>

// the call of function by CId expect the function not defined in the main 
     rule <k> get-main-function' ... </k>
	  <res-calc> Call(X:CId,list(L:List)) => listToK(L) ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <goto-map> Rho:Map </goto-map>
	  when notBool (X in keys(Rho))

//the call of function by pointer
// call the function block and save the function list 
     rule <k> get-main-function' ... </k>
	  <res-calc> Call(*X:CId,list(L:List)) => call-list-restriction(X,L) ~> S ~> listToK(L)  ... </res-calc>
	  <tmp-program-loc> Loc:K </tmp-program-loc>
	  <call-with-location> ... .Set => SetItem(call-loc(X,Loc)) </call-with-location>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <goto-map> ... 
		X |-> map ( funLabel(X) |-> gotoObject(_,_,S:K,_,_) _) 
	  ... </goto-map>

     rule <k> get-main-function' ... </k>
	  <res-calc> Call(X:CId,list(L:List)) => call-list-restriction(X,L) ~> S ~> listToK(L) ... </res-calc>
	  <tmp-program-loc> Loc:K </tmp-program-loc>
	  <call-with-location> ... .Set => SetItem(call-loc(X,Loc)) </call-with-location>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <goto-map> ... 
		X |-> map ( funLabel(X) |-> gotoObject(_,_,S:K,_,_) _) 
	  ... </goto-map>

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(Identifier(S:String),(ListItem(Call(Identifier(S1:String),list(L:List))) => L)_) ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set(.Set => SetItem(Identifier(S1)))) 
	  ... </capability>
	when (S2 ==K (S +String "_D"))
	     andBool (notBool (Identifier(S1) in Q))

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(Identifier(S:String),(ListItem(Call(Identifier(S1:String),list(L:List))) => L)_) ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set) 
	  ... </capability>
	when (Identifier(S1) in Q) andBool (S2 ==K (S +String "_D"))
	
     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(_,.List) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(_,(ListItem(_:CId) => .List) _) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(_,(ListItem(*_:CId) => .List)_) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(_,(ListItem(tv(_,_)) => .List)_) ...</res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(Identifier(S:String),(ListItem(Call(*Identifier(S1:String),list(L:List))) => L)_) ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set(.Set => SetItem(Identifier(S1)))) 
	  ... </capability>
	when (S2 ==K (S +String "_D"))
	     andBool (notBool (Identifier(S1) in Q))

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(Identifier(S:String),(ListItem(Call(*Identifier(S1:String),list(L:List))) => L)_) ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set) 
	  ... </capability>
	when (Identifier(S1) in Q) andBool (S2 ==K (S +String "_D"))

     rule <k> get-main-function' ... </k>
	  <res-calc> call-list-restriction(_, (ListItem(_:K._:K) => .List)_) ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (.K => call-struct(X,E)) ~> 
	         call-list-restriction(X:CId , (ListItem(&E:Expression) => .List)_) 
	  ... </res-calc> 

     rule <k> get-main-function' ... </k>
	  <res-calc> call-struct(Identifier(S1:String), X:CId._) => . ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <gtypes> ... 
			X |-> t(_,structType(F:CId,_,_))
	   ... </gtypes>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set(.Set => SetItem(F)))
	  ... </capability>
	  when S2 ==K (S1 +String "_L")
		andBool (notBool ( F in Q ))

     rule <k> get-main-function' ... </k>
	  <res-calc> call-struct(Identifier(S1:String),X:CId._) => . ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <gtypes> ... 
			X |-> t(_,structType(F:CId,_,_))
	   ... </gtypes>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set)
	  ... </capability>
	  when S2 ==K (S1 +String "_L")
		andBool ( F in Q )

     rule <k> get-main-function' ... </k>
	  <res-calc> call-struct(Identifier(S1:String),_) => . ... </res-calc>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> Rho:Map </capability>
	  when notBool ( (S1 +String "_L") in keys(Rho))
 
     rule <k> get-main-function' ... </k>
	  <res-calc> stringLiteral(_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> Identifier(_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> * Identifier(_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> & Identifier(_) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> & _:Expression => . ... </res-calc>
    
     rule <k> get-main-function' ... </k>
	  <res-calc> tv(_,_) => . ... </res-calc>

     syntax K ::= "re-locate" "(" K"," K ")"

     rule <k> get-main-function' ... </k>
	  <res-calc> (K1:K + K2:K) => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (K1:K - K2:K) => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (K1:K * K2:K) => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (K1:K / K2:K) => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (K1:K % K2:K) => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> K1:K := K2:K => K1 ~> re-locate(K2,Loc) ... </res-calc>
 	  <tmp-program-loc> Loc:K </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc> re-locate(K1:K,K2:K) => K1 ... </res-calc>
	  <tmp-program-loc> _ => K2 </tmp-program-loc>

     rule <k> get-main-function' ... </k>
	  <res-calc>  (X:CId.K:K) => K ... </res-calc>
	  <tmp-program-loc> Loc:K </tmp-program-loc>
	  <struct-with-location> ... .Set => SetItem(struct-loc(S,Loc)) </struct-with-location> 
	  <gtypes> ... X |-> t(_,structType(S:CId,_,_)) ... </gtypes>

     rule <k> get-main-function' ... </k>
	  <res-calc> * (K1:K + K2:K) => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (*((K1:K.K2:K)+K3:K)).K4:K => . ... </res-calc>

     rule <k> get-main-function' ... </k>
	  <res-calc> (*(*((K1:K.K2:K)+K3:K)+K4:K)).K5:K => . ... </res-calc>
/*******************   deal with the call-order information   *******************/ 
     rule <k> gcl-love ... </k>
         <block-pair> SetItem(in(M:Int,N:Int)) => SetItem(inCId(X,N)) ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <goto-map> ...
	     X:CId |-> map ( funLabel(X) |-> gotoObject(_,_,Block(M,_,_)~>_~>_,_,_) _)
	 ... </goto-map>
	 when M =/=Int N 
	
    rule <k> gcl-love ... </k>
         <block-pair> SetItem(in(M:Int,N:Int)) => .Set ... </block-pair>
	 when M ==Int N

    rule <k> gcl-love ... </k>
         <block-pair> SetItem(inCId(Identifier(S:String),N:Int))
	           => SetItem(inCId'(Identifier(S +String "_D"),N)) ... </block-pair>

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(inCId'(X:CId,N:Int)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ...
	      X |-> set(S:Set( .Set => SetItem(Y) ))
	 ... </capability>
	 <goto-map> ...
		     Y:CId |-> map ( funLabel(Y) |-> gotoObject(_,_,Block(N,_,_)~>_~>_,_,_)_)
	 ... </goto-map>
         when  notBool(Y in S)

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(inCId'(X:CId,N:Int)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ...
	      X |-> set( S:Set )
	 ... </capability>
	 <goto-map> ...
   	      Y:CId |-> map ( funLabel(Y) |-> gotoObject(_,_,Block(N,_,_)~>_~>_,_,_)_)
	 ... </goto-map>
         when  (Y in S)

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(inCId'(X:CId,_)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> Rho:Map </capability>
         when notBool(X in keys(Rho))
 
    rule <k> gcl-love ... </k>
 	 <block-pair> SetItem(out(M:Int,N:Int)) => SetItem(outCId(X,N))  ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <goto-map> ...
	     X:CId |-> map ( funLabel(X) |-> gotoObject(_,_,Block(M,_,_)~>_~>_,_,_)_)
	 ... </goto-map>

    rule <k> gcl-love ... </k>
 	 <block-pair> SetItem(outCId(Identifier(S:String),N:Int))
	           => SetItem(outCId'(Identifier(S +String "_D'"),N)) ... </block-pair>

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(outCId'(X:CId,N:Int)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ...
	      X |-> set( S:Set )
	 ... </capability>
	 <goto-map> ...
   	      Y:CId |-> map ( funLabel(Y) |-> gotoObject(_,_,Block(N,_,_)~>_~>_,_,_)_)
	 ... </goto-map>
         when  (Y in S)

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(outCId'(X:CId,N:Int)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ...
	      X |-> set( S:Set(.Set => SetItem(Y)) )
	 ... </capability>
	 <goto-map> ...
   	      Y:CId |-> map ( funLabel(Y) |-> gotoObject(_,_,Block(N,_,_)~>_~>_,_,_)_)
	 ... </goto-map>
         when  notBool(Y in S)

    rule <k> gcl-love ... </k>
	 <block-pair> SetItem(outCId'(X:CId,_)) => .Set ... </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> Rho:Map </capability>
         when notBool(X in keys(Rho))
	
    rule <k> gcl-love => get-res-struct(Q) ... </k>
	 <block-pair> .Set </block-pair>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <cap-point> Q:Set </cap-point>

    rule <k> get-res-struct(.Set) => finish-restriction(Q) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <cap-point> Q:Set </cap-point>

    rule <k> get-res-struct((SetItem(CabsLoc(_,_,_,_)) => .Set ) _ ) ... </k>

// the content of D' is the set of functions & struct that involved & struct involved by those functions
    rule <k> (.K => do-res-struct(Identifier(S1),Q1,Rho,call-loc(Identifier(S1),K),Q3)) ~> get-res-struct( (SetItem(Identifier(S1:String)) => .Set) _) ... </k>
	 <struct-with-location> Q3:Set </struct-with-location>
	 <call-with-location> ... 
		SetItem(call-loc(Identifier(S1),K:K))
	 ... </call-with-location>
	 <tmp-struct-restriction> Rho:Map </tmp-struct-restriction>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ... 
		Identifier(S2:String) |-> set(Q1:Set)
	 ... </capability>
	 when (S2 ==K  S1 +String "_D'")  andBool (S1 =/=K "main")

     rule <k> get-res-struct((SetItem(Identifier("main")) => .Set)_) ... </k>

    rule <k> (.K => add-res(Identifier(S:String),Q2)) ~> do-res-struct( Identifier(S:String),(SetItem(Identifier(S1:String)) => .Set) _,
			      _ ( Identifier(S2:String) |-> set(Q2:Set) => .Map ) _,
_,_) ... </k>
	when S2 ==K (S1 +String "_D")	

    rule <k> do-res-struct( _,(SetItem(Identifier(S1:String)) => .Set) _,Rho:Map,_,_) ... </k>
	when notBool ((S1 +String "_D") in keys(Rho))
	
    rule <k> add-res(Identifier(S:String) , (SetItem(X:CId) => .Set) _ ) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ... 
	   Identifier(S2:String) |-> set (Q:Set(.Set => SetItem(X))) 
	 ... </capability>
	when notBool (X in Q)
	     andBool S2 ==K (S +String "_D'")
	
    rule <k> add-res(Identifier(S:String), (SetItem(X:CId) => .Set) _ ) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ... 
	   Identifier(S2:String) |-> set (Q:Set) 
	 ... </capability>
	when  (X in Q)  andBool S2 ==K (S +String "_D'")
	
    rule <k> add-res(_ , .Set ) => . ... </k>

    rule <k> do-res-struct(_, .Set,_, call-loc(_,CabsLoc(_,I1:Int,_,_)),(SetItem(struct-loc(_, CabsLoc(_,I2:Int,_,_))) => .Set)_) ... </k>
	  when I1 >=Int I2

    rule <k> do-res-struct(_,.Set,_,call-loc(Identifier(S1:String),CabsLoc(_,I1:Int,_,_)),(SetItem(struct-loc(X:CId, CabsLoc(_,I2:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ... 
	   Identifier(S2:String) |-> set (Q:Set(.Set => SetItem(X))) 
	  ... </capability>
	  when I1 <Int I2 
	 	andBool S2 ==K (S1 +String "_D'") 
		andBool notBool (X in Q)

    rule <k> do-res-struct(_,.Set,_,call-loc(Identifier(S1:String),CabsLoc(_,I1:Int,_,_)),(SetItem(struct-loc(X:CId, CabsLoc(_,I2:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <capability> ... 
	   Identifier(S2:String) |-> set (Q:Set) 
	 ... </capability>
	  when I1 <Int I2 
	 	andBool S2 ==K (S1 +String "_D'") 
		andBool (X in Q)

    rule <k> do-res-struct(_,.Set,_,_,.Set) => . ... </k>

// finish point restriction for D
      rule <k> (.K => finish-restriction'(Identifier(S:String),Q1) 
		~> get-L (Identifier(S) , Q2)  )
		 ~> finish-restriction((SetItem(Identifier(S)) => .Set) _) ... </k>
	   <main-tu> SetItem(MainTu:String) </main-tu>	
	   <tu-id> MainTu </tu-id> 
	   <capability> ... 
			Identifier(S2:String) |-> set(Q1:Set)
			Identifier(S3:String) |-> set(Q2:Set) 
	   ... </capability>
	when S2 ==K (S +String "_D'") andBool ( S3 ==K (S +String "_L"))

      rule <k> finish-restriction((SetItem(CabsLoc(_,_,_,_)) => .Set)_) ... </k>
	
      rule <k> finish-restriction'(_, (SetItem(X:CId) => .Set)_) ... </k>
	   <main-tu> SetItem(MainTu:String) </main-tu>
	   <tu-id> MainTu </tu-id>
	   <gstructs> Rho:Map </gstructs>
	  when notBool (X in keys(Rho))

     rule <k> finish-restriction'(Identifier(S),(SetItem(X:CId) => .Set)_) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set)
	  ... </capability>
	  <gstructs> Rho:Map </gstructs>
	  when (X in keys(Rho)) 
		andBool (X in Q) 
		andBool (S2 ==K (S:String +String "_D"))

     rule <k> finish-restriction'(Identifier(S),(SetItem(X:CId) => .Set)_) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ... 
		Identifier(S2:String) |-> set(Q:Set(.Set => SetItem(X)))
	  ... </capability>
	  <gstructs> Rho:Map </gstructs>
	  when (X in keys(Rho)) 
		andBool ( notBool (X in Q))
		andBool (S2 ==K (S:String +String "_D"))

     rule <k> finish-restriction'(_,.Set) => . ... </k> 
 
     rule <k> get-L(Identifier(S:String),(SetItem(X:CId)=> .Set) _) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ...
		 Identifier(S2:String) |-> set(Q:Set(.Set => SetItem(X)))
	  ... </capability>
          when S2 ==K (S +String "_D")  andBool (notBool( X in Q))

     rule <k> get-L(Identifier(S:String),(SetItem(X:CId)=> .Set) _) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <capability> ...
		 Identifier(S2:String) |-> set(Q:Set)
	  ... </capability>
          when S2 ==K (S +String "_D")  andBool ( X in Q)

     rule <k> get-L(_,.Set) => . ... </k>

     rule <k> finish-restriction (.Set) => number-to-id ( keys(Rho) )... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <function-block> Rho:Map </function-block>
	  
     rule <k> number-to-id ((SetItem(I:Int) => .Set) _ ) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <function-block> ... ( I => X ) |-> _ ...</function-block>
	  <goto-map> ... 
		X:CId |-> map( funLabel(X) |-> gotoObject(_,_,Block(I,_,_)~>_~>_,_,_)_)
	  ... </goto-map>
	
     rule <k> number-to-id(.Set) => semantic-point-D ( Rho ) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <tu-id> MainTu </tu-id>
	  <semantic-points> Rho:Map </semantic-points>

     rule <k>  (.K => semantic-point-D'(I, Identifier(S), Q1, Q2)) ~> semantic-point-D((( (I:Int,Identifier(S)) |-> _) => .Map)_) ... </k>
	  <main-tu> SetItem(MainTu:String) </main-tu>
	  <call-with-location> Q1:Set </call-with-location>
	  <struct-with-location> Q2:Set </struct-with-location>
	  <tu-id> MainTu </tu-id>
	  <capability> ...
		Identifier(S2:String) |-> set(Q:Set)
	  ... </capability>
	  <semantic-points> ... 
		( I, Identifier(S:String)) |-> set ( _ => Q )
	  ... </semantic-points>
	when  (S2 ==K (S +String "_D"))


// before
    rule <k> semantic-point-D'(_, Y:CId, (SetItem(call-loc(_,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	when  (I1 <Int I2)

    rule <k> semantic-point-D'(_,Y:CId,_,(SetItem(struct-loc(_,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	when I1 <Int I2


// between 
    rule <k> semantic-point-D'(I:Int, Y:CId, (SetItem(call-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(_ (SetItem(X) => .Set) _)
	  ... </semantic-points>
	when I1 <=Int I andBool I1 >=Int I2 

    rule <k> semantic-point-D'(I:Int, Y:CId, (SetItem(call-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set)
	  ... </semantic-points>
	when I1 <=Int I andBool I1 >=Int I2 andBool (notBool (X in Q))

    rule <k> semantic-point-D'(I:Int, Y:CId, (SetItem(call-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set)
	  ... </semantic-points>
	when (I1 >=Int I andBool I1 <=Int I3)  andBool (X in Q)

    rule <k> semantic-point-D'(I:Int, Y:CId, (SetItem(call-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set(.Set => SetItem(X)))
	  ... </semantic-points>
	when (I1 >=Int I andBool I1 <=Int I3)  andBool ( notBool (X in Q))

    rule <k> semantic-point-D'(I:Int,Y:CId,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(_ (SetItem(X) => .Set) _)
	  ... </semantic-points>
	when I1 <=Int I andBool I1 >=Int I2

    rule <k> semantic-point-D'(I:Int,Y:CId,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(I2:Int, _ ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set)
	  ... </semantic-points>
	when I1 <=Int I andBool I1 >=Int I2 andBool (notBool (X in Q))

    rule <k> semantic-point-D'(I:Int,Y:CId,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set)
	  ... </semantic-points>
	when (I1 >=Int I andBool I1 <=Int I3)  andBool (X in Q)

    rule <k> semantic-point-D'(I:Int,Y:CId,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <semantic-points> ... 
		(I , Y) |-> set(Q:Set(.Set => SetItem(X)))
	  ... </semantic-points>
	when (I1 >=Int I andBool I1 <=Int I3)  andBool ( notBool (X in Q))

// after
    rule <k> semantic-point-D'(_, Y:CId, (SetItem(call-loc(_,CabsLoc(_,I1:Int,_,_))) => .Set)_,_) ...</k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	when I1 >Int I3

    rule <k> semantic-point-D'(_,Y:CId,_,(SetItem(struct-loc(_,CabsLoc(_,I1:Int,_,_))) => .Set)_) ... </k>
	 <function-block> ... 
		Y |-> begin-end(_ , I3:Int ) 
	 ... </function-block>
	when I1 >Int I3

    rule <k> semantic-point-D' (_,_,.Set,.Set) => . ... </k>
    rule <k> semantic-point-D (.Map) => check-pair ~> induced-point-D( keys(Rho) ) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> Rho:Map </induced-points>

    rule <k> check-pair => . ... </k>
	 <tmp-update-point> .Set </tmp-update-point>

    rule <k> (.K => ERROR("FD1","Single semantic point")) ~> check-pair ... </k>
	 <tmp-update-point>  SetItem(_:CabsLoc) </tmp-update-point>

    rule <k> (.K => induced-point-D'(I2,I1,I5,Q1,Q2)) 
	 ~>  induced-point-D( (SetItem(CabsLoc(_,I1:Int,_,_)) => .Set) _) ... </k>
	 <update-point-pair> ... 
		SetItem(point-pair(CabsLoc(_,I2:Int,_,_),CabsLoc(_,I3:Int,_,_)))
	 ... </update-point-pair>
	 <semantic-points> ... (I2, X:CId) |-> set(Q:Set) ... </semantic-points>
	 <function-block> ... X |-> begin-end(_ , I5:Int) ... </function-block>
	 <call-with-location> Q1:Set </call-with-location>
	 <struct-with-location> Q2:Set </struct-with-location>
	 <induced-points> ... CabsLoc(_,I1,_,_) |-> (_, _ => Q, _) ... </induced-points>
	 when I2 <Int I1 andBool I1 <Int I3

    rule <k> induced-point-D'(I1:Int,_,I3:Int,
		(SetItem(call-loc(_,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>
	 when I4 <=Int I1 orBool I4 >=Int I3

    rule <k> induced-point-D'(I1:Int,I2:Int,_,
		 (SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set,_)
	 ... </induced-points>
	 when I1 <Int I4 andBool I4 <Int I2 andBool (notBool (X in Q))
	
    rule <k> induced-point-D'(I1:Int,I2:Int,_,
		 (SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,_ (SetItem(X) => .Set )_,_)
	 ... </induced-points>
	 when I1 <Int I4 andBool I4 <Int I2  

    rule <k> induced-point-D'(_,I2:Int,I3:Int,
		 (SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set,_)
	 ... </induced-points> 
	when (X in Q) andBool I2 <Int I4 andBool I4 <Int I3 

    rule <k> induced-point-D'(_,I2:Int,I3:Int,
		 (SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set(.Set => SetItem(X)),_)
	 ... </induced-points> 
	when (notBool (X in Q)) andBool I2 <Int I4 andBool I4 <Int I3 
 
    rule <k> induced-point-D'(I1:Int,_,I3:Int,_,
		(SetItem(struct-loc(_,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>
	 when I4 <=Int I1 orBool I4 >=Int I3

    rule <k> induced-point-D'(I1:Int,I2:Int,_,_,
		(SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set,_)
	 ... </induced-points>
	 when I1 <Int I4 andBool I4 <Int I2 andBool (notBool (X in Q))
	
    rule <k> induced-point-D'(I1:Int,I2:Int,_,_,
		 (SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,_ (SetItem(X) => .Set )_,_)
	 ... </induced-points>
	 when I1 <Int I4 andBool I4 <Int I2  

    rule <k> induced-point-D'(_,I2:Int,I3:Int,_,
		 (SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set,_)
	 ... </induced-points> 
	when (X in Q) andBool I2 <Int I4 andBool I4 <Int I3 

    rule <k> induced-point-D'(_,I2:Int,I3:Int,_,
		 (SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... 	
		CabsLoc(_,I2,_,_) |-> (_,Q:Set(.Set => SetItem(X)),_)
	 ... </induced-points> 
	when (notBool (X in Q)) andBool I2 <Int I4 andBool I4 <Int I3

    rule <k> induced-point-D'(_,_,_,.Set,.Set) => . ... </k>

    rule <k> induced-point-D(.Set) => induced-contextual(keys(Rho)) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> Rho:Map </induced-points>

    rule <k> (.K => induced-contextual'(I1,I2,I3,Q1,Q2)) ~> induced-contextual((SetItem(CabsLoc(_,I2:Int,_,_)) => .Set)_) ... </k>
	 <update-point-pair> ... 
		SetItem(point-pair(CabsLoc(_,I1:Int,_,_),CabsLoc(_,I3:Int,_,_)))
	 ... </update-point-pair>
	 <call-with-location> Q1:Set </call-with-location>
	 <struct-with-location> Q2:Set </struct-with-location>
	 when I1 <Int I2 andBool I2 <Int I3

    rule <k> induced-contextual'(I1:Int,_,I3:Int,(SetItem(call-loc(_,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 when I4 >=Int I3 orBool I1 >=Int I4

    rule <k> induced-contextual'(I1:Int,I2:Int,_,(SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (Q:Set(.Set => SetItem(X)),_,_) ... </induced-points>
	 when I1 <=Int I4 andBool I4 <=Int I2 andBool (notBool (X in Q))

    rule <k> induced-contextual'(I1:Int,I2:Int,_,(SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (Q:Set,_,_) ... </induced-points>
	 when I1 <=Int I4 andBool I4 <=Int I2 andBool (X in Q)

    rule <k> induced-contextual'(_,I2:Int,I3:Int,(SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (_,_,Q:Set(.Set => SetItem(X))_) ... </induced-points>
	 when I2 <=Int I4 andBool I4 <=Int I3 andBool (notBool (X in Q))

    rule <k> induced-contextual'(_,I2:Int,I3:Int,(SetItem(call-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_,_) ... </k>	
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (_,_,Q:Set) ... </induced-points>
	 when I2 <=Int I4 andBool I3 <=Int I2 andBool (X in Q)

    rule <k> induced-contextual'(I1:Int,_,I3:Int,_,(SetItem(struct-loc(_,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>	
	 when I4 >=Int I3 orBool I1 >=Int I4

    rule <k> induced-contextual'(I1:Int,I2:Int,_,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (Q:Set(.Set => SetItem(X)),_,_) ... </induced-points>
	 when I1 <=Int I4 andBool I4 <=Int I2 andBool (notBool (X in Q))

    rule <k> induced-contextual'(I1:Int,I2:Int,_,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (Q:Set,_,_) ... </induced-points>
	 when I1 <=Int I4 andBool I4 <=Int I2 andBool (X in Q)

    rule <k> induced-contextual'(_,I2:Int,I3:Int,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (_,_,Q:Set(.Set => SetItem(X))_) ... </induced-points>
	 when I2 <=Int I4 andBool I4 <=Int I3 andBool (notBool (X in Q))

    rule <k> induced-contextual'(_,I2:Int,I3:Int,_,(SetItem(struct-loc(X:CId,CabsLoc(_,I4:Int,_,_))) => .Set)_) ... </k>
	 <main-tu> SetItem(MainTu:String) </main-tu>
	 <tu-id> MainTu </tu-id>
	 <induced-points> ... CabsLoc(_,I2,_,_) |-> (_,_,Q:Set) ... </induced-points>
	 when I2 <=Int I4 andBool I3 <=Int I2 andBool (X in Q)

    rule <k> induced-contextual'(_,_,_,.Set,.Set) => . ... </k>
    rule <k> induced-contextual (.Set) => get-global (keys(Rho)) ... </k>
	 <patch-unit> SetItem(Patch:String) </patch-unit>
	 <tu-id> Patch </tu-id>
	 <genv> Rho:Map </genv>

    rule <k> get-global((SetItem(X:CId) => .Set) _) ... </k>
	 <patch-unit> SetItem(Patch:String) </patch-unit>
	 <tu-id> Patch </tu-id>
	 <genv> ... X |-> _ @ link(_) </genv>

    rule <k> get-global((SetItem(X:CId) => .Set)_) ... </k>
	 <patch-unit> SetItem(Patch:String) </patch-unit>
	 <tu-id> Patch </tu-id>
	 <genv> ... X |-> _ @ static (_) </genv>
         <gtypes> ... X |-> T:Type ... </gtypes>
	 when isFunctionType(T)

    rule <k> get-global((SetItem(X:CId) => .Set)_) ... </k>
	 <patch-unit> SetItem(Patch:String) </patch-unit>
	 <tu-id> Patch </tu-id>
	 <genv> ... X |-> _ @ static (_) </genv>
         <gtypes> ... X |-> T:Type ... </gtypes>
	 <wanted> ... (.Set => SetItem((X, "CId"))) </wanted>
	 when  notBool isFunctionType(T)

    rule <k> get-global(.Set) => . ... </k>






/* stuff about the struct init  */
//for local struct init
	rule	<goto-map> ... 
		_ |-> map ( _  |-> gotoObject ( _, _, Block(_, _, list( _
			ListItem(CodeLoc(
  			DeclarationDefinition ( InitNameGroup(_, list( ListItem( InitName (Name ( _ , _ ), CompoundInit( list( 
		        L:List => 
			ListItem (InitFragment( NextInit, SingleInit( tv( 0 , t(.Set,int)))))
			ListItem (InitFragment( NextInit, CompoundInit( list(
						ListItem(InitFragment(InFieldInit(Identifier("data"),NextInit),CompoundInit(list(L))))))))			
		   ))))))) ,Loc:K))_))~>_~>_ ,_ ,_ ))
	     ... </goto-map>
		 <tmp-loc-for-struct-init> S:Set(.Set => SetItem(Loc)) </tmp-loc-for-struct-init>
		when notBool (Loc in S)

//for global struct init
	rule <k>  CodeLoc(
  			DeclarationDefinition ( InitNameGroup(Specifier ( list ( _ ListItem(StructRef ( _ )) _ ) ), list( ListItem( InitName (Name ( _ , _ ), CompoundInit( list( 
		        L:List => 
			ListItem (InitFragment( NextInit, SingleInit( tv( 0 , t(.Set,int)))))
			ListItem (InitFragment( NextInit, CompoundInit( list(
						ListItem(InitFragment(InFieldInit(Identifier("data"),NextInit),CompoundInit(list(L))))))))			
		   ))))))) ,Loc:K) 
		    ... </k>
	     <curr-function>  file-scope </curr-function>
	     <tmp-loc-for-struct-init> S:Set(.Set => SetItem(Loc)) </tmp-loc-for-struct-init>
             when notBool (Loc in S)
	  
	rule <k> (check-struct-version(X:CId,Loc:K,_) ~> nclv(Sym:SymLoc, T:Type) . F:CId ) 
			=> nclv(Sym, T) . Identifier("udata") . Identifier("data"). F:CId ... </k>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <patch-unit> Pa:Set </patch-unit>
	     <original-struct> S:Set </original-struct>
	     <tmp-loc-for-struct-init> Q:Set </tmp-loc-for-struct-init>
	when notBool (Loc in Q)
	     andBool (X in S) 
	     andBool (notBool Tu in Pa)

	rule <k> check-struct-version(_,_,_) => . ... </k>
	     <curr-tu> Patch:String </curr-tu>
	     <patch-unit> SetItem(Patch) </patch-unit>

	rule <k> lookupField (X:CId,Loc:SymLoc,Q:Set,Y:CId,fieldInfo(_ ListItem(typedDeclaration(_,Z:CId))_,_,_) ,Fields:FieldInfo) 
		 => nclv(Loc,t(Q,structType(Y,9999,Fields))) .Identifier("udata") .Identifier("data") .X ... </k>
	  //   <curr-tu> Tu:String </curr-tu>
	    // <patch-unit> Pa:Set </patch-unit>
	when Z ==K Identifier("version") andBool (X =/=K Identifier("version")  orBool X =/=K Identifier("udata"))
	     //andBool (notBool(Tu in Pa))

	rule <k> check-struct-version(X:CId,Loc:K,_) => .  ... </k>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <original-struct> S:Set </original-struct>
	     <tmp-loc-for-struct-init> Q:Set </tmp-loc-for-struct-init>
	when notBool(X in S) 	
	     orBool (Loc in Q)

	rule <k> check-struct ~> get-main-function  => . ... </k>
	     <curr-tu> Patch-String </curr-tu>
	     <patch-unit> SetItem(Patch) </patch-unit>

endmodule
