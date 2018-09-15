module C-CONFIGURATION
     imports C-SYNTAX
     imports C-DYNAMIC-SYNTAX
     imports C-TRANSLATION-INIT-SYNTAX
     imports COMPAT-SYNTAX
     imports C-TRANSLATION-STMT-UPDATE-SYNTAX

     configuration 
<global>
     <mem> .Map </mem>
     <functions color="lightgray"> .Map </functions>

     <main-tu color="lightgray"> .Set </main-tu>
     <patch-unit> .Set </patch-unit>

     // CId |-> Types
     <external-types> .Map </external-types>
     // CId |-> Loc
     <external-defs> .Map </external-defs>

     <linking-state>
          // CId |-> Set(TUs)
          <external-decls> .Map </external-decls>
          // CIds
          <external-uses> SetItem(Identifier("main")) </external-uses>
     </linking-state>

     // dummy link base |-> real base
     <linkings> .Map </linkings>

     <translation-units>
          <tu multiplicity="*">
               <tu-id> "" </tu-id>
               <genv color="lightgray"> .Map </genv>
               <gtypes color="lightgray"> .Map </gtypes>
               <gstructs color="lightgray"> .Map </gstructs>

               // kpair(CId, BlockNum) |-> SymBase
               <local-statics> .Map </local-statics>
               // kpair(CId, BlockNum) |-> Type
               <local-types> .Map </local-types>
               // kpair(CId, BlockNum) |-> FieldInfo
               <local-structs> .Map </local-structs>

               <tu-linking-state>
                    <externals> .Map </externals>
                    <internals> .Map </internals>
                    <next-link-loc> .K </next-link-loc>
                    <next-static-loc> .K </next-static-loc>
               </tu-linking-state>

		<update>
			<version> 0 </version>                           // save the version of the program 
			<wanted> .Set </wanted>   			 // the set of the content in patch that need to be updated 
			<wanted-struct> .Set </wanted-struct>            // the set of new struct 
			<capability> .Map </capability>    		 // the restriction of each update point
			<struct-restriction> .Map </struct-restriction>  // the restriction of each function in the program
			<cap-point> .Set </cap-point>		         // the set of the updatepoint
			<original-struct> .Set </original-struct>  	 // record all struct in the program
			<original-func> .Set </original-func>		 // the function name (used to match and change) 
			<patch-tu> .Set </patch-tu>
			<semantic-points> .Map </semantic-points>         // update point |-> D 
			<induced-points> .Map </induced-points>          // the Map of induced update point (alpha, D, omga)
			<update-point-pair> .Set </update-point-pair>    // semantic update points pair specified by programmer 
		</update>

               <next-unnamed color="black"> 0 </next-unnamed>

               <goto-map color="lightgray"> .Map </goto-map>

               // TODO(chathhorn): move.
               <incomplete-tags> .Set </incomplete-tags>
          </tu>
     </translation-units>
</global>
<T multiplicity="?">
<exec>
     // SymLoc |-> Type
     <effective-types> .Map </effective-types>

     <k color="green" multiplicity="?">
          $PGM:K
          ~> load(unwrapObj($OBJ1:Bag), unwrapObj($OBJ2:Bag))
          ~> link
          ~> check-restriction       // D & D' & L  
          ~> cleanup
	  
     </k>

	<updating>
	<signal>
		<signal-for-updatepatch> false </signal-for-updatepatch>
		// <signal-for-updatepoint> false </signal-for-updatepoint>
		<signal-for-struct>  false </signal-for-struct>
		<signal-for-check-struct-version> false </signal-for-check-struct-version>
	</signal>
	<cap-points> .Set </cap-points> // the set of capability
	<do-restriction-check> .List </do-restriction-check>
	<original-function> .Set </original-function>
	<struct-content> .Set </struct-content>
	<tmp-loc-for-struct-init> .Set </tmp-loc-for-struct-init>
	<tmp-update-point> .Set </tmp-update-point>			// for paired semantic update points 
	<restriction-calc>
		<res-calc> .K </res-calc>
		<pbinding> .Map </pbinding>   // 保存参数绑定信息
		<function-pointer> .List </function-pointer>    // save  function pointer 同下 
		<fp-func> .Set </fp-func>                       // 保存涉及函数指针作为参数的函数的block number
		<local-struct-var> .Map </local-struct-var>
		<ava-pointer> .Set </ava-pointer>   // 保存所有指针名称
		<ava-live> .List </ava-live>
		<save-area> .List </save-area>
		<for-ava> .List </for-ava>
		<res-block-history> .List </res-block-history>
		<recent-out-block> .Set </recent-out-block>
		<block-pair> .Set </block-pair>
		<curr-functions> .List </curr-functions>
		<past-functions> .List </past-functions> 
		<tmp-struct-restriction> .Map </tmp-struct-restriction>  // struct Id |-> set(SetItem(function id))
		<tmp-program-loc> .K </tmp-program-loc>
		<struct-with-location> .Set </struct-with-location>      // (struct Id , location )
		<call-with-location> .Set </call-with-location>          // (function id, location )
		<function-block> .Map </function-block>
	</restriction-calc>
	</updating>

     <final-computation multiplicity="?" color="lightgray">
          .K
     </final-computation>

     <goto-map-calc color="cyan">
          <goto-calc multiplicity="*" color="cyan">
               <computation color="cyan"> .K </computation>
               <computation-tail color="cyan">
                    .K
               </computation-tail>
               <decl-stack color="cyan">
                    .List
               </decl-stack>
               <goto-nesting-depth color="cyan">
                    0
               </goto-nesting-depth>
               <goto-block-history color="cyan">
                    .List
               </goto-block-history>
               <goto-loop-stack color="cyan">
                    .List
               </goto-loop-stack>
          </goto-calc>
     </goto-map-calc>
     <control>
          <curr-tu color="lightgray"> "" </curr-tu>
          <curr-function color="lightgray">
               file-scope
          </curr-function>
          <curr-program-loc color="black">
               UnknownCabsLoc
          </curr-program-loc>

          // Toggle to allow writes and other special treatment for
          // initializers.
          <initializing> 0 </initializing>

          <control-details> // TODO(chathhorn): dumb name
               <local>
                    // maps from CIds
                    <env color="red"> .Map </env>
                    <types color="lightgray"> .Map </types>
                    <structs color="lightgray"> .Map </structs>
                    <block-history> .List </block-history>
               </local>
               <block-stack color="violet"> .List </block-stack>

               // Used to figure initializers.
               <curr-object color="cyan">
                    .List
               </curr-object>
               <curr-subobject color="cyan">
                    .List
               </curr-subobject>
               <incomplete-length color="cyan">
                    0
               </incomplete-length>
               <saved-init color="cyan">
                    .K
               </saved-init>

               // Used for typing expressions.
               <type multiplicity="?" color="cyan"> .K </type>
               // Holds the innermost type while we unroll the
               // type around it.
               <decl-type-holder color="cyan">
                    .K
               </decl-type-holder>
          </control-details>        
     </control>

</exec>

<error-cell multiplicity="?" color="black"> .K </error-cell>

<status> initializing </status>

<options> $OPTIONS:Set </options>

</T>
          
endmodule
