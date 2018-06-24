module C-UPDATE
     imports C-TYPING-CANONICALIZATION-SYNTAX
     imports C-TYPING-SYNTAX
     imports C-TYPING-CANONICALIZATION

     imports C-SYNTAX
     imports C-DYNAMIC-SYNTAX
     imports C-BITSIZE-SYNTAX
     imports C-COMMON-EXPR-ALIGNOF-SYNTAX
     imports COMPAT-SYNTAX
     imports DEBUG-SYNTAX
     imports C-TYPING-INTERPRETATION-SYNTAX

/********************************************************************/
/* stuff about restriction of struct in the /common/exper/members.k */
/********************************************************************/


	syntax K ::= "(" CId "," String ")"
	
	rule <k> (.K => StructDef(Identifier(S +String "_old"), L))
          ~> canonicalizeSpecifier(BagItem(
               StructDef(Identifier(S:String), L:K) => StructRef(Identifier(S +String "_old")))) ...</k>
	     <curr-tu> Tu:String </curr-tu>
	     <signal-for-updatepatch> false </signal-for-updatepatch>
	     <signal-for-struct> false </signal-for-struct>
	     <curr-function> file-scope </curr-function>
	     <tu-id> Tu </tu-id>
	     <original-struct> .Set => SetItem(Identifier(S)) ... </original-struct>
	     <struct-content> .Set => SetItem(Identifier(S))  ... </struct-content>
          when Identifier(S) =/=K Identifier("")
		andBool (Identifier(S) =/=K Identifier("FILE_")) 
          [structural] 

        rule <k> (.K => StructDef(Identifier(S +String "_old"), L))
          ~> canonicalizeSpecifier(BagItem(
               StructDef(Identifier(S:String), L:K) => StructRef(Identifier(S +String "_old")))) ... </k>
	     <signal-for-updatepatch> true </signal-for-updatepatch>
	     <signal-for-struct> false </signal-for-struct>
	     <struct-content> .Set => SetItem(Identifier(S))  ... </struct-content>
	     <curr-tu> Tu:String </curr-tu>
	     <tu-id> Tu </tu-id>
	     <wanted> ... .Set => SetItem((Identifier(S),"struct")) </wanted>
	     <wanted-struct> ... .Set => SetItem(Identifier(S)) </wanted-struct>
          when   Identifier(S) =/=K Identifier("") 
		andBool Identifier(S) =/=K Identifier("FILE_")
          [structural] 

        rule <k> (.K => StructDef(Identifier(S), L))
             ~> canonicalizeSpecifier(BagItem(
                 StructDef(Identifier(S:String), L:K) => StructRef(Identifier(S)))) ... </k> 
	     <curr-function> F:CId </curr-function>
          when   F =/=K file-scope 
          [structural]

        rule (.K => StructDef(Identifier(S), L))
             ~> canonicalizeSpecifier(BagItem(
                  StructDef(Identifier(S:String), L:K) => StructRef(Identifier(S)))) 
       	     when   Identifier(S) ==K Identifier("FILE_")
              [structural] 

        rule <k> (.K => StructDef(Identifier(S), L))
             ~> canonicalizeSpecifier(BagItem(
                  StructDef(Identifier(S:String), L:K) => StructRef(Identifier(S)))) ... </k>
	     <signal-for-struct> true </signal-for-struct>

	syntax K ::=  "declare-other-struct"  | "declare-other-struct'"

	rule <k> T:Type ~> discard' => T ~> discard ~> declare-other-struct ... </k>
	     [prefer]  

	rule <k> declare-other-struct =>   
              OnlyTypedef (Specifier ( 
	      list (
			ListItem(StructDef (Identifier(S) , 
				list ( 
					ListItem(FieldGroup (Specifier ( list ( ListItem(Unsigned) ListItem(Int) ) ) , list ( ListItem(FieldName ( Name ( Identifier ( "version" ) , JustBase ) )) ) )) 
					ListItem(FieldGroup (Specifier ( list ( ListItem(UnionDef ( Identifier ( "" ) , list ( 
							ListItem(FieldGroup (Specifier ( list ( ListItem(StructRef (Identifier(S +String "_old"))) ) ) , list ( ListItem(FieldName ( Name ( Identifier ( "data" ) , JustBase ) )) ) ))
							ListItem(FieldGroup (Specifier ( list ( ListItem(Char) ) ), list ( ListItem(FieldName ( Name ( Identifier ( "padding") , ArrayType ( JustBase , tv ( 50 , t ( .Set , int ) ) , Specifier ( list ( .List ) )) )))))) 
))))) , 
list (ListItem(FieldName ( Name ( Identifier ( "udata" ) , JustBase ) )) ) 
))
)
)))
)) ~> declare-other-struct'    ... </k>
	     <struct-content> SetItem(Identifier(S:String)) => .Set ... </struct-content>
	     <signal-for-struct> false => true </signal-for-struct>

   	rule <k> declare-other-struct' => declare-other-struct ... </k>
             <signal-for-struct> true => false </signal-for-struct>
 
  	 rule <k> declare-other-struct => . ... </k>
       	      <struct-content> .Set </struct-content>

endmodule 
