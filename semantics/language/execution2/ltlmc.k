require "builtins/model-checker.k"

module C-LTLMC-SYNTAX
     imports LTL-HOOKS
     imports MODEL-CHECKER-HOOKS
     imports C-BITS-SYNTAX

     // Ltl atomic propositions.
     syntax ValueProp ::= Int  
                        | ptr(SymLoc, Type)
                        | struct(List, FieldInfo)
                        | union(List, FieldInfo)

     syntax CProp ::= ValueProp  | CId	
                    | "-" CProp
                    | "+" CProp
                    | "*" CProp
                    > CProp "[" CProp "]"
                    | CProp "." CId
//  		    | CProp "->" CId
                    > CProp "*" CProp [left]
                    | CProp "/" CProp [left]
                    > CProp "+" CProp [left]
                    | CProp "-" CProp [left]
//                    > CProp "<" CProp  [left]
//                    | CProp "<=" CProp [left]
//                    | CProp ">" CProp  [left]
//                    | CProp ">=" CProp [left]
                    > CProp "==" CProp [left]
                    | CProp "!=" CProp [left]

     syntax Prop ::= CProp | Bool | "__running" | "__error"  | "__update"
    
     syntax   CId ::= "x" [token]
		    | "y" [token]
		    | "lightNS" [token]
	 	    | "lightEW" [token]
  //   syntax   Cprop ::= "a" [token]




endmodule

module C-LTLMC
     imports C-LTLMC-SYNTAX
     imports C-SYNTAX
     imports C-DYNAMIC-SYNTAX
     imports C-TYPING-SYNTAX
     imports C-BITS-SYNTAX
     imports C-ENV-SYNTAX
     imports C-BITSIZE-SYNTAX
     imports C-DECL-INITIALIZER-SYNTAX

     imports C-MEMORY-ALLOC-SYNTAX
     imports C-MEMORY-READING-SYNTAX
     imports C-MEMORY-WRITING-SYNTAX

     imports C-SYMLOC-SYNTAX
     imports C-SETTINGS-SYNTAX
     imports COMPAT-SYNTAX

     rule <generatedTop>...
	       <T> ...
               <status> mainCalled </status>
     	       ... </T> 
          ...</generatedTop>
	  |=Ltl __running
	=> true 			    [ltl, anywhere] 

     rule <generatedTop>... 
	       <T> ...
                <update-signal> true </update-signal>
               ... </T>
	  ...</generatedTop>
          |=Ltl __update		
	=> true 			   [ltl, anywhere] 

     rule <generatedTop>... 
	     <T>...
               <error-cell> _ </error-cell> 
             ...</T> 
          ...</generatedTop>
	  |=Ltl __error
	=> true 			   [ltl, anywhere] 

     rule _:Bag |=Ltl P:Bool => P          [ltl, anywhere]
 
     rule B:Bag |=Ltl P:CProp => boolify(ltlRVal(B,P)) [ltl, anywhere]

     syntax Bool ::= "boolify" "(" ValueProp ")"    
     rule boolify(I:Int) => notBool(I ==Int 0)      [ltl, anywhere]

     syntax ValueProp ::= "ltlRVal""(" Bag "," CProp")"

     rule ltlRVal(B:Bag, - P:CProp)  => ltlRVal(B, 0 - ltlRVal(B, P)) [ltl, anywhere] 
     rule ltlRVal(B:Bag, + P:CProp)  => ltlRVal(B, P)                 [ltl, anywhere] 

     rule ltlRVal(_, L:Int * R:Int) => L *Int R	 		 [ltl, anywhere] 
     rule ltlRVal(_, L:Int / R:Int) => L /Int R	 		 [ltl, anywhere] 
     rule ltlRVal(_, L:Int + R:Int) => L +Int R	 		 [ltl, anywhere] 
     rule ltlRVal(_, L:Int - R:Int) => L -Int R	 		 [ltl, anywhere] 

     syntax Int ::= "intify" "(" Bool ")"
     //rule ltlRVal(_, L:Int <  R:Int) =>  intify(L <Int  R)	 [ltl, anywhere] 
     //rule ltlRVal(_, L:Int <= R:Int) =>  intify(L <=Int R)	 [ltl, anywhere] 
     //rule ltlRVal(_, L:Int >  R:Int) =>  intify(L >Int  R)	 [ltl, anywhere] 
     //rule ltlRVal(_, L:Int >= R:Int) =>  intify(L >=Int R)	 [ltl, anywhere] 
     rule ltlRVal(_, L:Int == R:Int) =>  intify(L ==Int R)	 [ltl, anywhere] 
     rule ltlRVal(_, L:Int != R:Int) =>  intify(L =/=Int R)	 [ltl, anywhere] 
     rule intify(true)  => 1 					 [ltl, anywhere]
     rule intify(false) => 0 					 [ltl,anywhere]

     rule ltlRVal(_, V:ValueProp) => V                           [ltl, anywhere] 


     rule ltlRVal(B:Bag, L:CProp[R:CProp])
          => ltlRVal(B, * (L + R)) [ltl, anywhere] 
     
     // "strictness"
     rule ltlRVal(B:Bag, _:KLabel(P:CProp => ltlRVal(B, P)))
          when notBool (isValueProp(P) ==K true)          [ltl, anywhere] 
     rule ltlRVal(B:Bag, _:KLabel((L:CProp => ltlRVal(B, L)),, _))
          when notBool (isValueProp(L) ==K true)		 [ltl, anywhere] 
     rule ltlRVal(B:Bag, Lbl:KLabel(_,, (R:CProp => ltlRVal(B, R))))
          when notBool (isValueProp(R) ==K true)
               andBool (Lbl =/=KLabel '_._)
               andBool (Lbl =/=KLabel '_->_)	 [ltl, anywhere] 

     rule ltlRVal(B:Bag, * ptr(L:SymLoc, T:Type))
          => ltlRVal(B, dumbRead(B, L, T))	 [ltl, anywhere] 
/*
     rule ltlRVal(B:Bag, P:CProp -> X:CId)
          => ltlRVal(B, (* P) . X)	 [ltl, anywhere] 

     rule ltlRVal(_,
          struct(V:List,
               fieldInfo(_, (_ X |-> T:Type), (_ X |-> Offset:Int))
          ) . X:CId)
          => joinBytes(T, 
               fillToBytes-aux(
                    extractBitsFromList-aux(
                         dataList(explodeToBits(V)), 
                         Offset *Int cfg:bitsPerByte,
                         bitSizeofType(T), .List),
                    .List))	 [ltl, anywhere] 
     rule ltlRVal(_,
          union(V:List,
               fieldInfo(_, (_ X |-> T:Type), (_ X |-> Offset:Int))
          ) . X:CId)
          => joinBytes(T, 
               fillToBytes-aux(
                    extractBitsFromList-aux(
                         dataList(explodeToBits(V)), 
                         Offset, bitSizeofType(T), .List),
                    .List))	 [ltl, anywhere] 
*/

     syntax Int ::= dumbRead(Bag, SymLoc, Type) [function]
     syntax Int ::= "dumbRead'" "(" Map "," SymLoc "," Type "," Int "," List ")" 
          [function]

    rule ltlRVal(B:Bag, X:CId) => ltlRVal(B, * ltlLVal(B, X))  [ltl, anywhere] 
    rule dumbRead(
               <generatedTop>... <global>... 
                    <mem> Mem:Map </mem> 
               ...</global> ...</generatedTop>, 
               Loc:SymLoc, T:Type) 
          => dumbRead'(Mem, stripProv(Loc), T, byteSizeofType(T), .List)	 [ltl, anywhere] 

     rule dumbRead'(
          (_ Base |-> object(_, _, (_ Offset |-> V:K))), 
          loc(Base:SymBase, (Offset:Int => Offset +Int 1)), 
          _, 
          (NBytes:Int => NBytes -Int 1), 
          _:List (.List => ListItem(V)))
          when NBytes >Int 0
	 [ltl, anywhere] 

     syntax ValueProp ::= joinBytes(Type, K) [function]
     syntax ValueProp ::= "joinBytes'" "(" Type "," List "," List ")" [function]
     rule dumbRead'(
          _,
          _,
          T:Type,
          0,
          Bytes:List)
          => joinBytes(T, dataList(Bytes))
	 [ltl, anywhere] 
     rule joinBytes(T:Type, dataList(L:List)) 
          => joinBytes'(T, L, ListItem(piece(0,0)))
	 [ltl, anywhere] 
     rule joinBytes(t(_, pointerType(T:Type)), 
               dataList(ListItem(piece(subObject(L:SymLoc, _, _), _)) _:List))
          => ptr(L, T) 	 [ltl, anywhere] 
     rule joinBytes(t(_, structType(_, _, Info:FieldInfo)), dataList(V:List))
          => struct(V, Info) 	 [ltl, anywhere] 
     rule joinBytes(t(_, unionType(_, _, Info:FieldInfo)), dataList(V:List))
          => union(V, Info)	 [ltl, anywhere] 
     rule joinBytes(T:Type, dataList(V:List))
          => joinBytes'(T, V, .List)
          when hasIntegerType(T)
	 [ltl, anywhere] 
     rule joinBytes'(T:Type, 
               L:List ListItem(piece(N:Int, Len:Int)), 
               ListItem(piece(N':Int, Len':Int)))
          => joinBytes'(T, L, ListItem(piece(
               piece(N', Len') bit:: piece(N, Len), Len +Int Len')))	[ltl, anywhere] 

     rule joinBytes'(_, .List, ListItem(piece(N:Int, _))) => N	 [ltl, anywhere] 

     // Not so interested in l-values.
     syntax ValueProp ::= "ltlLVal" "(" Bag "," CId ")"	    [function]
     syntax ValueProp ::= "ltlLVal'" "(" Bag "," String ")" [function]
 
     rule ltlLVal(B:Bag, X:CId) => ltlLVal'(B, "y") 
	  when X ==K y [ltl, anywhere]

     rule ltlLVal(B:Bag, X:CId) => ltlLVal'(B, "x") 
	  when X ==K x [ltl, anywhere]	 

     rule ltlLVal(B:Bag, X:CId) => ltlLVal'(B, "lightNS") 
	  when X ==K lightNS [ltl, anywhere]	

     rule ltlLVal(B:Bag, X:CId) => ltlLVal'(B, "lightEW") 
	  when X ==K lightEW [ltl, anywhere]	  

     rule ltlLVal'(
          <generatedTop>... <global> ... 
	  <external-defs> ... 
		Identifier(S) |-> Base:SymBase
	  ... </external-defs>
	  <external-types> ...
	        Identifier(S) |-> T:Type
	  ... </external-types>	
	  ... </global> ...</generatedTop>, 
          S:String)
          => ptr(loc(Base,0) , T)      [ltl, anywhere] 

endmodule
