module C-COMMON-EXPR-MEMBERS
     imports C-BITSIZE-SYNTAX
     imports C-BITS-SYNTAX
     imports C-DECL-INITIALIZER-SYNTAX
     imports C-DYNAMIC-SYNTAX     //nclv, lv, 
     imports C-ENV-SYNTAX
     imports C-ERROR-SYNTAX
     imports C-MEMORY-READING-SYNTAX
     imports C-MEMORY-WRITING-SYNTAX
     imports C-SETTINGS-SYNTAX
     imports C-SYMLOC-SYNTAX
     imports C-SYNTAX
     imports C-TYPING-SYNTAX   // completetags
     imports COMPAT-SYNTAX
     imports C-UPDATE

     /*@ \fromStandard{\source[n1570]{\para{6.5.2.3}{3}}}{
     A postfix expression followed by the \cinline{.} operator and an
     identifier designates a member of a structure or union object. The value
     is that of the named member, and is an lvalue if the first expression is
     an lvalue. If the first expression has qualified type, the result has the
     so-qualified version of the type of the designated member.
     }*/

     syntax K ::= "(" CId "," K ")"


// check struct version
// if this struct has not been checked then check it (restriction is the program location)
     rule <k> (.K => check-struct-version(S,Loc,Base)) ~> nclv(loc(Base:K,_),t(_, structType(S:CId, _, _))) . _:K ~> _:K ... </k>
	 <signal-for-check-struct-version> false => true </signal-for-check-struct-version>
	 <curr-program-loc> Loc:K </curr-program-loc>
/*
     rule <k>( nclv(loc(Base:K,I1:Int),t(Q:Set, structType(S:CId, I2:Int, Fields:FieldInfo))) . X:K . Y:CId =>
	      check-struct-version(S,Loc,Base) ~> nclv(loc(Base,I1),t(Q,structType(S,I2,Fields))) .X .Identifier("udata"). Identifier("data") .Y) ~> _:K ... </k>
	  <signal-for-check-struct-version> false => true </signal-for-check-struct-version>
	  <curr-program-loc> Loc:K </curr-program-loc>
*/
// global
     rule <k> nclv(Loc:SymLoc, t(Mods:Set,
                    structType(S:CId, _, Fields:FieldInfo))) . F:CId
               => lookupField(F, Loc, Mods, S, Fields, Fields)
          ...</k>
	  <signal-for-updatepatch> false </signal-for-updatepatch>
          <initializing> I:Int </initializing>
	  <curr-function> file-scope </curr-function>
          when ( notBool (Atomic in Mods)
               orBool I >Int 0 )
          [structural]	

//local 
// this is the first element occur
     rule <k> nclv(Loc:SymLoc, t(Mods:Set,
                    structType(S:CId, _, Fields:FieldInfo))) . F:CId
               => lookupField(F, Loc, Mods, S, Fields, Fields)
          ...</k>
          <initializing> I:Int </initializing>
	  <signal-for-updatepatch> false </signal-for-updatepatch>
	  <curr-function> Identifier(Str:String) </curr-function>
	  <curr-tu> Tu:String </curr-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> Rho:Map(.Map => Identifier(Str +String "_D") |-> set(SetItem(S))) </struct-restriction>
          when ( notBool (Atomic in Mods)
               orBool I >Int 0 )
	       andBool notBool (Identifier(Str +String "_D") in keys(Rho) )
          [structural]

// this is the follower
     rule <k> nclv(Loc:SymLoc, t(Mods:Set,
                    structType(S:CId, _, Fields:FieldInfo))) . F:CId
               => lookupField(F, Loc, Mods, S, Fields, Fields)
          ...</k>
	  <signal-for-updatepatch> false </signal-for-updatepatch>
          <initializing> I:Int </initializing>
	  <curr-function> Identifier(S1:String) </curr-function>
	  <curr-tu> Tu:String </curr-tu>
	  <tu-id> Tu </tu-id>
	  <struct-restriction> ... Identifier(S2:String) |-> set(_ (.Set => SetItem(S))) ... </struct-restriction>
          when ( notBool (Atomic in Mods)
               orBool I >Int 0 )
	       andBool (S1 +String "_D") ==K S2
          [structural]

// when in the patch 
     rule <k> nclv(Loc:SymLoc, t(Mods:Set,
                    structType(Identifier(S:String), _, _))) . F:CId
               => lookupField(F,Loc,Mods,Identifier(S2),Fields,Fields)   
          ...</k>
          <initializing> I:Int </initializing>
	  <signal-for-updatepatch> true </signal-for-updatepatch>
	 // <wanted>  Q:Set( .Set => SetItem((Identifier(S),"struct"))) </wanted>
	  <gstructs> ... 
		Identifier(S2:String) |-> Fields:FieldInfo
	  ... </gstructs>
          when ( notBool (Atomic in Mods)
               orBool I >Int 0 ) andBool ( S2 ==K (S +String "_old"))

     rule <k> nclv(Loc:SymLoc, t(Mods:Set,
                    unionType(S:CId, _, Fields:FieldInfo))) . F:CId
               => lookupField(F, addProv(fromUnion(Loc, F, Fields), Loc),
                    Mods, S, Fields, Fields)
          ...</k>
          <initializing> I:Int </initializing>
          when notBool (Atomic in Mods)
               orBool I >Int 0
          [structural]
     rule <k> (. => UNDEF("CEM1",
               "attempting to access a member in an atomic struct.",
               "6.5.2.3:5"))
               ~> nclv(_, t(Mods:Set, structType(_, _, _))) . _:CId
          ...</k>
          <initializing> 0 </initializing>
          when Atomic in Mods
          [structural]
     rule <k> (. => UNDEF("CEM2",
               "attempting to access a member in an atomic union.",
               "6.5.2.3:5"))
               ~> nclv(_, t(Mods:Set, unionType(_, _, _))) . _:CId
          ...</k>
          <initializing> 0 </initializing>
          when Atomic in Mods
          [structural]

     // The last two parameters are for convenience and should be the same.
     // TODO(chathhorn): anonymous structs/unions.
     syntax K ::= lookupField(CId, SymLoc, Set, CId, FieldInfo, FieldInfo)
          [function]

     rule lookupField(F:CId, Loc:SymLoc, Mods:Set, S:CId, Fields:FieldInfo,
          fieldInfo(_,
               F |-> T:Type _,
               F |-> Offset:Int _))
          // Complete recursive struct/union definitions.
          => lv(Loc +bytes Offset,
               completeTag(S, Fields, addQualifiers(Mods, T)))

     // Same deal as above, only for byte lists.
     rule tv(agg(L:List), t(Mods:Set,
               structType(S:CId, _, Fields:FieldInfo))) . F:CId
          => extractField(F, L, Mods, S, Fields, Fields)
          [structural]
     rule tv(agg(L:List), t(Mods:Set,
               unionType(S:CId, _, Fields:FieldInfo))) . F:CId
          => extractField(F, L, Mods, S, Fields, Fields)
          [structural]

     syntax K ::= extractField(CId, List, Set, CId, FieldInfo, FieldInfo)
          [function]

     rule extractField(F:CId, L:List, Mods:Set, S:CId, Fields:FieldInfo,
          fieldInfo(_,
               F |-> t(Mods':Set, T':SimpleType) _,
               F |-> Offset:Int _))
          => concretize(completeTag(S, Fields, t(Mods Mods', T')),
               fillToBytes(extractBitsFromList(dataList(L),
                    Offset *Int cfg:bitsPerByte,
                    bitSizeofType(completeTag(S, Fields, t(Mods Mods', T'))))))

     /*@ \fromStandard{\source[n1570]{\para{6.5.2.3}{4}}}{
     A postfix expression followed by the \cinline{->} operator and an
     identifier designates a member of a structure or union object. The value
     is that of the named member of the object to which the first expression
     points, and is an lvalue. \broken{If the first expression is a pointer to
     a qualified type, the result has the so-qualified version of the type of
     the designated member.}
     }*/

     // the difference between -> and . is pointer and variable .
     rule K:K -> F:CId => (* K) . F [macro, structural]

     /*@ \fromStandard{\source[n1570]{\para{6.5.2.1}{2--3}}}{
     A postfix expression followed by an expression in square brackets
     \cinline{[]} is a subscripted designation of an element of an array
     object. The definition of the subscript operator \cinline{[]} is that
     \cinline{E1[E2]} is identical to \cinline{(*((E1)+(E2)))}. Because of the
     conversion rules that apply to the binary \cinline{+} operator, if
     \cinline{E1} is an array object (equivalently, a pointer to the initial
     element of an array object) and \cinline{E2} is an integer,
     \cinline{E1[E2]} designates the \cinline{E2}-th element of \cinline{E1}
     (counting from zero).

     Successive subscript operators designate an element of a multidimensional
     array object. If \cinline{E} is an $n$-dimensional array ($n \ge 2$) with
     dimensions $i \times j \times\cdots\times k$, then \cinline{E} (used as
     other than an lvalue) is converted to a pointer to an ($n -
     1$)-dimensional array with dimensions $j \times\cdots\times k$. If the
     unary \cinline{*} operator is applied to this pointer explicitly, or
     implicitly as a result of subscripting, the result is the referenced ($n -
     1$)-dimensional array, which itself is converted into a pointer if used as
     other than an lvalue. It follows from this that arrays are stored in
     row-major order (last subscript varies fastest).
     }*/
     rule E1:K[E2:K] => *(E1 + E2) 
          [macro, structural]

endmodule
