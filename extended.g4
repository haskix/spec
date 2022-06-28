grammar Haskix;

tokens {
	TightInfixAt,
	PrefixTilde,
	PrefixBang,
	SuffixBang,
	PrefixMinus,
	PrefixProj /*-- RecordDotSyntax*/,
	TightInfixProj /*-- RecordDotSyntax*/,
	PrefixAt,
	PrefixPercent /*-- for linear types*/,
	SimpleQuote /*-- 'x*/,

	LowerName,
	UpperName,
	VarSymbol,
	ConstructorSymbol,

	IPDUPVarId,
	LabelVarId,

	// literal
	Char,
	String,
	Integer,
	Rational,
	PrimChar,
	PrimString,
	PrimInteger,
	PrimWord,
	PrimFloat,
	PrimDouble,

	PrefixDollar,
	PrefixDollarDollar,
	TH_TYQuote,
	TH_QuasiQuote,
	TH_QQuasiQuote
}

// -- Exported parsers %name parseModuleNoHaddock module %name parseSignature signature %name
// parseImport importdecl %name parseStatement e_stmt %name parseDeclaration topdecl %name
// parseExpression exp %name parsePattern pat %name parseTypeSignature sigdecl %name parseStmt
// maybe_stmt %name parseIdentifier identifier %name parseType ktype %name parseBackpack backpack
// %partial parseHeader header

// root node and module body
root: mod_attrib* top_decl*;

//---------------------------------------------------------------------------
// Module

// The place for module deprecation is really too restrictive, but if it was allowed at its natural
// place just before 'module', we get an ugly s/r conflict with the second alternative. Another
// solution would be the introduction of a new pragma DEPRECATED_MODULE, but this is not very nice,
// either, and DEPRECATED is only expected to be used by people who really know what they are doing.
// :-)
module_id: UpperName;

module_path: ('flake' | 'super' | module_id) (
		'.' ('super' | module_id)
	)*;

module_expr: module_path;

module_decl: attribute* 'module' module_id mod_body? ';';

mod_body: 'where'? '{' root '}' | '=' module_expr;

//---------------------------------------------------------------------------
// Import Declarations

rename_spec:
	qualified_var 'as' (var | var_op)
	| o_qual_type_con_no_var_con 'as' (type_con | type_con_op)
	| 'type' ordinary_qual_type_con 'as' (type_con | type_con_op)
	| 'pattern' qualified_con 'as' (con | con_op);

open_decl:
	attribute* 'open' module_path ('.' import_tree | rename_spec)? ';';

import_tree:
	'using' '{' (import_tree ';')* '}'
	| (module_id | 'super') ('.' import_tree)?
	| 'self'
	| var
	| o_qual_type_con_no_var_con
	| 'type' ordinary_qual_type_con
	| 'pattern' qualified_con
	| rename_spec;

// -------------------------------------------------------------------------- Visibility
// declarations

visibility:
	('private' | 'public') (
		'(' ('flake' | 'self' | 'super' | 'in' module_path) ')'
	)?;

block_header: visibility? 'block' 'where'?;

//---------------------------------------------------------------------------
// Precedence Group Declarations

precedence_group: var_id;
qualified_precedence_group: qualifier? precedence_group;

qual_prec_groups:
	qualified_precedence_group (',' qualified_precedence_group)*;

prec_group_decl:
	'precedence' precedence_group 'where'? '{' (
		'above' '=' '[' qual_prec_groups ']' ';'
	)? ('below' '=' '[' qual_prec_groups ']' ';')? (
		'assoc' '=' ('Left' | 'Right' | 'None') ';'
	)? '}' ';';

ops: op (',' op)*;

fixity_decl: 'infix' qualified_precedence_group ops ';';
//---------------------------------------------------------------------------
// Top-Level Declarations

top_decl:
	visibility? module_decl
	| visibility? open_decl
	| visibility? class_decl
	| visibility? type_top_decl
	| visibility? prec_group_decl
	| standalone_kind_sig
	| instance_decl
	| standalone_deriving
	| role_annotion
	| visibility? 'foreign' fdecl
	| '{-# RULES' rule+ '#-}' ';'
	| decl_no_th
	| attribute* block_header '{' top_decl* '}' ';'

	// Template Haskell Extension The $(..) form is one possible form of infixexp but we treat an
	// arbitrary expression just as if it had a $(..) wrapped around it
	| infix_exp;

class_decl:
	attribute* 'class' type_class_header functional_deps 'where'? '{' (
		associated_family_decl
		| decl
		| 'default' infix_exp ':' sig_type ';'
	)* '}' ';';
functional_deps: ('|' functional_dep (',' functional_dep)*)?;
functional_dep: type_var* '->' type_var*;

type_top_decl: // ordinary type synonyms
	attribute* 'type' type '=' forall_type_with_kind ';'
	// Note ktype, not sigtype, on the right of '=' We allow an explicit for-all but we don't insert
	// one in type Foo a = (b,b) Instead we just say b is out of scope
	// 
	// Note the use of type for the head; this allows infix type constructors to be declared
	| attribute* 'type' 'family' type type_family_kind_sig? injective_info (
		'where'? '{' (ty_fam_inst_eqn* | '..') '}'
	)? ';'
	| attribute* data_or_newtype capi_ctype type_class_header kind_sig? (
		constrs
		| gadt_constr_list
		| record
	) ';'
	| attribute* 'data' 'family' type data_family_kind_sig? ';';

// Injective type families
injective_info: ( '|' injectivity_cond)?;
injectivity_cond: type_var_id '->' type_var_id+;

instance_decl:
	attribute* 'instance' instance_type (
		'where'? '{' (associated_instance_decl | decl)* '}'
	)? ';'

	// type instance declarations
	| attribute* 'type' 'instance' ty_fam_inst_eqn ';'

	// GADT instance declaration
	| attribute* data_or_newtype 'instance' capi_ctype family_instance_header kind_sig? (
		constrs
		| gadt_constr_list
		| record
	) ';';

standalone_kind_sig:
	'type' (ordinary_qual_type_con (',' ordinary_qual_type_con)*) ':' sig_type_with_kind ';';

// Closed type families

ty_fam_inst_eqn: ('forall' type_var_binder+ '.')? type '=' forall_type_with_kind ';';
// Note the use of type for the head; this allows infix type constructors and type patterns

associated_family_decl:
	'data' 'family'? type data_family_kind_sig? ';'
	| 'type' 'family'? type at_kind_inj_sig? ';'
	| 'type' 'instance'? ty_fam_inst_eqn;
// default intances

associated_instance_decl:
	'type' 'instance'? ty_fam_inst_eqn ';'
	// Note the use of type for the head; this allows infix type constructors and type patterns
	| data_or_newtype 'instance'? capi_ctype family_instance_header kind_sig? (
		constrs
		| gadt_constr_list
		| record
	) ';';

data_or_newtype: 'data' | 'newtype';

// Family result/return kind signatures

kind_sig: ':' kind;

data_family_kind_sig: ':' kind;

type_family_kind_sig: ':' kind | '=' type_var_binder;

at_kind_inj_sig:
	| ':' kind
	| '=' type_var_binder_no_braces '|' injectivity_cond;

// tycl_hdr parses the header of a class or data type decl, which takes the form T a b Eq a => T a
// (Eq a, Ord b) => T a b T Int [a] -- for associated types Rather a lot of inlining here, else we
// get reduce/reduce errors
type_class_header: (context '=>')? type;

family_instance_header:
	('forall' type_var_binder+ '.')? (context '=>')? type;

capi_ctype: ('{-# CTYPE' String String? '#-}')?;

//---------------------------------------------------------------------------
// Datatype declarations

gadt_constr_list:
	'where'? '{' (
		gadt_constr
		| block_header '{' gadt_constr* '}' ';'
	)* deriving* '}';

gadt_constr: attribute* visibility? con_list ':' sig_type ';';

// We allow the following forms: C :: Eq a => a -> T a C :: forall a. Eq a => !a -> T a D { x,y :: a
// } :: T a forall a. Eq a => D { x,y :: a } :: T a

constrs:
	'where'? '{' (
		constructor
		| block_header '{' constructor* '}' ';'
	)* deriving* '}';

constructor:
	'|' attribute* visibility? forall? (context '=>')? constr_stuff ';';

forall: 'forall' type_var_binder+ '.';

record: 'where'? '{' record_body deriving* '}';

constr_stuff: infix_type;

//---------------------------------------------------------------------------
// deriving

deriving:
	attribute* (
		'deriving' deriv_clause_types
		| 'deriving' deriv_strategy_no_via deriv_clause_types
		| 'deriving' deriv_clause_types deriv_strategy_via
	) ';';

deriv_clause_types:
	qualified_type_con
	| '(' ')'
	| '(' deriv_types ')';
deriv_strategy_no_via: 'stock' | 'anyclass' | 'newtype';

deriv_strategy_via: 'via' sig_type_with_kind;

standalone_deriving:
	attribute* 'deriving' deriv_standalone_strategy 'instance' instance_type ';';
deriv_standalone_strategy: (
		'stock'
		| 'anyclass'
		| 'newtype'
		| deriv_strategy_via
	)?;
//---------------------------------------------------------------------------
// Role annotations

role_annotion: 'type' 'role' ordinary_qual_type_con role+ ';';

// read it in as a varid for better error messages
role: LowerName | '_';

qvarcon: qualified_var | qualified_con;

//---------------------------------------------------------------------------
// Nested declarations

// Binding groups other than those of class and instance declarations

binds:
	// May have implicit parameters No type declarations:
	'{' (decl | dbind)+ '}';

where_binds:
	// May have implicit parameters No type declarations:
	'where' binds;

//---------------------------------------------------------------------------
// Transformation Rules

rule: String rule_activation rule_foralls infix_exp '=' exp ';';

// Rules can be specified to be NeverActive, unlike inline/specialize pragmas
rule_activation: rule_explicit_activation?;

// This production is used to parse the tilde syntax in pragmas such as * {-# INLINE[~2] ... #-} *
// {-# SPECIALISE [~ 001] ... #-} * {-# RULES ... [~0] ... g #-} Note that it can be written either
// without a space [~1] (the PREFIX_TILDE case), or with a space [~ 1] (the VARSYM case). See Note
// [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
rule_activation_marker: PrefixTilde | VarSymbol;

rule_explicit_activation:
	'[' Integer ']'
	| '[' rule_activation_marker Integer? ']';

rule_foralls: ('forall' rule_var* '.' ('forall' rule_var* '.')?)?;

rule_var: var_id | '(' var_id ':' forall_type ')';

/* Note [Parsing explicit foralls in Rules] ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ We really
 want the above definition of rule_foralls to be: rule_foralls : 'forall' tv_bndrs '.' 'forall'
 rule_vars '.' | 'forall' rule_vars '.' | {- empty -} where rule_vars (term variables) can be named
 "forall", "family", or "role", but tv_vars (type variables) cannot be. However, such a definition
 results in a reduce/reduce conflict. For example, when parsing: > {-# RULE "name" forall a ... #-}
 before the '...' it is impossible to determine whether we should be in the first or second case of
 the above. This is resolved by using rule_vars (which is more general) for both, and ensuring that
 type-level quantified variables do not have the names "forall", "family", or "role" in the function
 'checkRuleTyVarBndrNames' in GHC.Parser.PostProcess. Thus, whenever the definition of tyvarid (used
 for tv_bndrs) is changed relative to varid (used for rule_vars), 'checkRuleTyVarBndrNames' must be
 updated.
 */

//---------------------------------------------------------------------------
// Foreign import and export declarations

fdecl:
	attribute* (
		'import' callconv safety fspec ';'
		| 'import' callconv fspec ';'
		| 'export' callconv fspec ';'
	);

callconv: 'stdcall' | 'ccall' | 'capi' | 'prim' | 'javascript';

safety: 'unsafe' | 'safe' | 'interruptible';

fspec: String? var ':' sig_type;
// if the entity string is missing, it defaults to the empty string; the meaning of an empty entity
// string depends on the calling convention

//---------------------------------------------------------------------------
// Type signatures

sig: ':' forall_type;

opt_tyconsig: ( ':' general_type_con)?;

// Like ktype, but for types that obey the forall-or-nothing rule. 
sig_type_with_kind: sig_type | forall_type ':' kind;

// Like ctype, but for types that obey the forall-or-nothing rule. 
sig_type: forall_type;

sig_vars: var (',' var)*;

sigtypes1: sig_type (',' sig_type)*;
//---------------------------------------------------------------------------
// Types

unpackedness: '{-# UNPACK' '#-}' | '{-# NOUNPACK' '#-}';

forall_telescope: 'forall' type_var_binder+ ('.' | '->');

forall_type_with_kind: forall_type (':' kind)?;

forall_type:
	forall_telescope forall_type
	| context '=>' forall_type
	| ipvar ':' forall_type
	| type;

//--------------------
// Notes for 'context' We parse a context as a btype so that we don't get reduce/reduce errors in
// ctype. The basic problem is that (Eq a, Ord a) looks so much like a tuple type. We can't tell
// until we find the =>

context: b_type;

/* Note [GADT decl discards annotations] ~~~~~~~~~~~~~~~~~~~~~ The type production for btype `->`
 ctype add the AnnRarrow annotation twice, in different places. This is because if the type is
 processed as usual, it belongs on the annotations for the type as a whole. But if the type is
 passed to mkGadtDecl, it discards the top level SrcSpan, and the top-level annotation will be
 disconnected. Hence for this specific case it is connected to the first type too.
 */

type:
	b_type /*shift*/
	| b_type mult? '->' forall_type
	| b_type '->.' forall_type;

mult: PrefixPercent arg_type;

b_type: infix_type;

infix_type:
	type_apply /*%shift*/
	| type_apply type_op infix_type
	| unpackedness infix_type;

type_apply:
	arg_type
	| type_op
	| type_apply type_arg
	| type_apply PrefixAt arg_type;

type_arg: unpackedness? arg_type;

type_op:
	qual_type_con_op
	| type_var_op
	| SimpleQuote qualified_con_op
	| SimpleQuote var_op;

arg_type:
	n_unit_general_type_con //- Not including unit tuples
	| type_var /*%shift*/ //- (See Note [Unit tuples])
	| '*'
	| PrefixTilde arg_type
	| PrefixBang arg_type
	| 'with'? record_type
	// Constructor sigs only
	| '(' ')'
	| '(' forall_type_with_kind ',' comma_types1 ')'
	| '(#' '#)'
	| '(#' comma_types1 '#)'
	| '(#' forall_type_with_kind ('|' forall_type_with_kind)+ '#)'
	| '[' forall_type_with_kind ']'
	| '(' forall_type_with_kind ')'
	| quasiquote
	| splice_untyped
	| SimpleQuote qual_con_no_wiredlist
	| SimpleQuote '(' forall_type_with_kind ',' comma_types1 ')'
	| SimpleQuote '[' comma_types1? ']'
	| SimpleQuote var
	// Two or more [ty, ty, ty] must be a promoted list type, just as if you had written '[ty, ty,
	// ty] (One means a list type, zero means the list type constructor, so you have to quote
	// those.)
	| '[' forall_type_with_kind ',' comma_types1 ']'
	| Integer
	| Char
	| String
	| '_';

record_type: '{' record_body '}';

record_body: (field_type | block_header '{' field_type* '}' ';')*;

field_type: attribute* sig_vars ':' forall_type ';';

// An inst_type is what occurs in the head of an instance decl e.g. (Foo a, Gaz b) => Wibble a b
// It's kept as a single type for convenience.
instance_type: sig_type;

deriv_types: sig_type_with_kind (',' sig_type_with_kind)*;

comma_types1:
	forall_type_with_kind (',' forall_type_with_kind)*;

type_var_binder:
	type_var_binder_no_braces
	| '{' type_var (':' kind)? '}';

type_var_binder_no_braces: type_var | '(' type_var ':' kind ')';

//---------------------------------------------------------------------------
// Kinds
kind: forall_type;

//---------------------------------------------------------------------------
// Value definitions

/* Note [Declaration/signature overlap] ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ There's an awkward
 overlap with a type signature. Consider f :: Int -> Int = ...rhs... Then we can't tell whether it's
 a type signature or a value definition with a result signature until we see the '='. So we have to
 inline enough to postpone reductions until we know.
 */

/*
 ATTENTION: Dirty Hackery Ahead! If the second alternative of vars is var instead of qvar, we get
 another shift/reduce-conflict. Consider the following programs: { (^^) :: Int->Int ; } Type
 signature; only var allowed { (^^) :: Int->Int = ... ; } Value defn with result signature; qvar
 allowed (because of instance decls) We can't tell whether to reduce var to qvar until after we've
 read the signatures.
 */

decl_no_th:
	sig_decl
	| attribute* infix_exp sig? rhs ';'
	| pattern_synonym_decl;

decl:
	decl_no_th
	// Why do we only allow naked declaration splices in top-level declarations and not here? Short
	// answer: because readFail009 fails terribly with a panic in cvBindsAndSigs otherwise.
	| splice_exp ';';

rhs: ('=' exp | gdrh+) where_binds?;

gdrh: '|' guard_quals '=' exp;

sig_decl:
	// See Note [Declaration/signature overlap] for why we need infixexp here
	infix_exp ':' sig_type ';'
	| var ',' sig_vars ':' sig_type ';'
	| fixity_decl
	| pattern_synonym_sig ';'
	| '{-# COMPLETE' con_list opt_tyconsig '#-}' ';'
	// This rule is for both INLINE and INLINABLE pragmas
	| '{-# INLINE' activation qvarcon '#-}' ';'
	| '{-# SPECIALISE' activation qualified_var ':' sigtypes1 '#-}' ';'
	| '{-# SPECIALISE_INLINE' activation qualified_var ':' sigtypes1 '#-}' ';'
	| '{-# SPECIALISE' 'instance' instance_type '#-}' ';'

	// A minimal complete definition
	| '{-# MINIMAL' name_boolformula? '#-}' ';';

activation: explicit_activation?;

explicit_activation: //- In brackets
	'[' rule_activation_marker? Integer ']';

//---------------------------------------------------------------------------
// Expressions

quasiquote: TH_QuasiQuote | TH_QQuasiQuote;

exp:
	infix_exp ':' forall_type
	| infix_exp '-<' exp
	| infix_exp '>-' exp
	| infix_exp '-<<' exp
	| infix_exp '>>-' exp
	| infix_exp /*shift*/;

infix_exp: exp10 | infix_exp qualified_op exp10;

exp10: '-'? fun_exp;

fun_exp:
	fun_exp arg_exp
	| fun_exp PrefixAt arg_type
	| 'static' arg_exp
	| arg_exp;

arg_exp:
	qualified_var TightInfixAt arg_exp
	| PrefixTilde arg_exp
	| PrefixBang arg_exp
	| arg_exp SuffixBang // expr! same as x<-expr; x 
	| PrefixMinus arg_exp
	| '\\' arg_pattern* '->' exp
	| 'let' binds 'in' exp
	| '\\' 'case' alts_list
	| 'if' exp 'then' exp 'else' exp
	| 'if' '{' guard_pattern+ '}'
	| 'case' exp 'of'? alts_list
	// QualifiedDo.
	| (qualifier? 'do') stmt_list
	| (qualifier? 'mdo') stmt_list
	| 'proc' arg_exp '->' exp
	| arg_exp1;

arg_exp1:
	arg_exp1 'with'? '{' field_binds '}'
	| arg_exp1 TightInfixProj field
	| arg_exp2;

arg_exp2:
	qualified_var
	| qualified_con
	| ipvar /*shift */
	| overloaded_label
	| literal
	// This will enable overloaded strings permanently. Normally the renamer turns HsString into
	// HsOverLit when -XOverloadedStrings is on. | STRING { sL (getLoc $1) (HsOverLit $!
	// mkHsIsString (getSTRINGs $1) (getSTRING $1) noExtField) }
	| Integer
	| Rational
	// N.B.: sections get parsed by these next two productions. This allows you to write, e.g., '(+
	// 3, 4 -)', which isn't correct Haskell (you'd have to write '((+ 3), (4 -))') but the less
	// cluttered version fell out of having texps.
	| '(' tuple_exp ')'
	| 'record' ('(' deriv_types ')')? 'with'? '{' (
		attribute* field_bind
	)* '}'
	| '(' tuple_exprs ')'
	| '(' projection ')'
	| '(#' tuple_exp '#)'
	| '(#' tuple_exprs '#)'
	| '[' list ']'
	| '_'
	// Template Haskell Extension
	| splice_untyped
	| splice_typed
	| SimpleQuote qualified_var
	| SimpleQuote qualified_con
	| SimpleQuote type_var
	| TH_TYQuote general_type_con
	| TH_TYQuote /*shift */
	| '[|' exp '|]'
	| '[||' exp '||]'
	| '[t|' forall_type_with_kind '|]'
	| '[p|' infix_exp '|]'
	| '[d|' '{' top_decl* '}' '|]'
	| quasiquote
	// arrow notation extension
	| '(|' arg_exp acmd* '|)';

projection: projection TightInfixProj field | PrefixProj field;

splice_exp: splice_untyped | splice_typed;

splice_untyped: PrefixDollar arg_exp2;

splice_typed: PrefixDollarDollar arg_exp2;

acmd: arg_exp;

//---------------------------------------------------------------------------
// Tuple expressions

// "texp" is short for tuple expressions: things that can appear unparenthesized as long as they're
// inside parens or delimited by commas
tuple_exp:
	exp
	// Note [Parsing sections] ~~~~~~~~~~~~~~~~~~~~~~~ We include left and right sections here,
	// which isn't technically right according to the Haskell standard. For example (3 +, True)
	// isn't legal. However, we want to parse bang patterns like (!x, !y) and it's convenient to do
	// so here as a section Then when converting expr to pattern we unravel it again Meanwhile, the
	// renamer checks that real sections appear inside parens.
	| infix_exp qualified_op
	| qopm infix_exp
	// View patterns get parenthesized above
	| exp '->' tuple_exp;

// Always at least one comma or bar. Though this can parse just commas (without any expressions), it
// won't in practice, because (,,,) is parsed as a name. See Note [ExplicitTuple] in GHC.Hs.Expr.
tuple_exprs:
	tuple_exp? commas_tup_tail
	| tuple_exp '|'+
	| '|'+ tuple_exp '|'*;

// Always starts with commas; always follows an expr
commas_tup_tail: ','+ tup_tail?;

// Always follows a comma
tup_tail: tuple_exp commas_tup_tail?;

//---------------------------------------------------------------------------
// List expressions

list:
	tuple_exp
	| lexps
	| tuple_exp '..'
	| tuple_exp ',' exp '..'
	| tuple_exp '..' exp
	| tuple_exp ',' exp '..' exp
	| tuple_exp ('|' squals)+;

lexps: (lexps | tuple_exp) ',' tuple_exp;

//---------------------------------------------------------------------------
// List Comprehensions

squals: // one can "grab" the earlier ones
	squals ',' transform_qual
	| squals ',' qual
	| transform_qual
	| qual;
// | transformquals1 ',' '{|' pquals '|}' { sLL $1 $> ($4 : unLoc $1) } | '{|' pquals '|}' { sL1 $1
// [$2] }

// It is possible to enable bracketing (associating) qualifier lists by uncommenting the lines with
// {| |} above. Due to a lack of consensus on the syntax, this feature is not being used until we
// get user demand.

transform_qual: // Function is applied to a list of stmts *in order*
	'then' exp ('by' exp)?
	| 'then' 'group' ('by' exp)? 'using' exp;

//---------------------------------------------------------------------------
// Guards

guard_quals: qual (',' qual)+;

//---------------------------------------------------------------------------
// Case alternatives

alts_list:
	'{' (
		pattern /* <- multiway if is not allowed  */ alt_rhs ';'
	)* '}';

alt_rhs: '->' exp where_binds? | guard_pattern+ where_binds?;

guard_pattern: '|' guard_quals '->' exp ';';

//--------------------------------------------------------------------------------
// Patterns

// 'pat' recognises a pattern, including one with a bang at the top e.g. "!x" or "!(x,y)" or "C a b"
// etc Bangs inside are parsed as infix operator applications, so that we parse them right when
// bang-patterns are off
pattern: exp;

bind_pattern: exp;

arg_pattern: arg_exp;

// Pattern synonyms

pattern_synonym_decl:
	'pattern' pattern_synonym_lhs '=' pattern ';'
	| 'pattern' pattern_synonym_lhs '<-' pattern (
		'where'? '{' decl* '}'
	)? ';';

pattern_synonym_lhs:
	con var_id*
	| var_id con_op var_id
	| con '{' var (',' var)* '}';

pattern_synonym_sig: 'pattern' con_list ':' sig_type;
//---------------------------------------------------------------------------
// Statement sequences

stmt_list: '{' stmt* '}';

e_stmt: stmt;

stmt: qual ';' | 'rec' stmt_list ';';

qual: bind_pattern '<-' exp | exp | 'let' binds;

//---------------------------------------------------------------------------
// Record Field Update/Construction

field_binds: field_bind* ('..' ';')?;

field_bind:
	var '=' tuple_exp ';'
	// RHS is a 'texp', allowing view patterns (#6038) and, incidentally, sections. Eg f (R { x =
	// show -> s }) = ...
	| var ';'
	// In the punning case, use a place-holder The renamer fills in the final value

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer AZ: need to pull out the
	// let block into a helper
	| field (TightInfixProj field)+ '=' tuple_exp ';'
	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer AZ: need to pull out the
	// let block into a helper
	| field (TightInfixProj field)+ ';';

//---------------------------------------------------------------------------
// Implicit Parameter Bindings

dbind: ipvar '=' exp ';';

ipvar: IPDUPVarId;

//---------------------------------------------------------------------------
// Overloaded labels
overloaded_label: LabelVarId;

//---------------------------------------------------------------------------
// Attributes

attribute: '{-@' String exp '@-}';

mod_attrib: '{-@ MOD' String exp '@-}';

//---------------------------------------------------------------------------
// Warnings and deprecations

name_boolformula:
	name_boolformula_and ('|' name_boolformula_and)*;

name_boolformula_and: name_boolformula_and_list;

name_boolformula_and_list:
	name_boolformula_atom (',' name_boolformula_atom)*;

name_boolformula_atom: '(' name_boolformula ')' | name_var;

name_list: name_var (',' name_var)*;

name_var: var | con;

//---------------------------------------
// Data constructors

// There are two different productions here as lifted list constructors are parsed differently. See
// Note [ExplicitTuple] in GHC.Hs.Expr
sysd_con_nolist: //- Wired in data constructors
	'(' ')'
	| '(' ','+ ')'
	| '(#' '#)'
	| '(#' ','+ '#)';

// See Note [Empty lists] in GHC.Hs.Expr
sysd_con: sysd_con_nolist | '[' ']';

qual_con_no_wiredlist: gen_qual_con | sysd_con_nolist;

gen_qual_con:
	qualified_constructor_id
	| '(' qualified_constructor_symbol ')';

con: constructor_id | '(' constructor_symbol ')' | sysd_con;

qualified_con: gen_qual_con | sysd_con;

con_list: con (',' con)*;

con_op: constructor_symbol | '`' constructor_id '`';

qualified_con_op:
	qualified_constructor_symbol
	| '`' qualified_constructor_id '`';

//--------------------------------------------------------------------------
// Type constructors

// See Note [Unit tuples] in GHC.Hs.Type for the distinction between gtycon and ntgtycon * A
/** "general" qualified tycon, including unit tuples*/
general_type_con: n_unit_general_type_con | '(' ')' | '(#' '#)';

/** A "general" qualified tycon, excluding unit tuples */
n_unit_general_type_con:
	ordinary_qual_type_con
	| '(' ','+ ')'
	| '(#' ','+ '#)'
	| '(#' '|'+ '#)'
	| '(' '->' ')'
	| '[' ']';

ordinary_qual_type_con:
	qualified_type_con
	| '(' qual_type_con_symbol ')';
// These can appear in export lists

/** Type constructor which cannot be mistaken */
o_qual_type_con_no_var_con:
	qualified_type_con
	| '(' qualifier? ConstructorSymbol ')';
// for variable constructor in export lists see Note [Type constructors in export list]: qtycon | '(' QCONSYM ')' | '(' CONSYM ')' | '(' ':' ')';

/* Note [Type constructors in export list] ~~~~~~~~~~~~~~~~~~~~~ Mixing type constructors and data
 constructors in export lists introduces ambiguity in grammar: e.g. (*) may be both a type
 constructor and a function. -XExplicitNamespaces allows to disambiguate by explicitly prefixing
 type constructors with 'type' keyword. This ambiguity causes reduce/reduce conflicts in parser,
 which are always resolved in favour of data constructors. To get rid of conflicts we demand that
 ambiguous type constructors (those, which are formed by the same productions as variable
 constructors) are always prefixed with 'type' keyword. Unambiguous type constructors may occur both
 with or without 'type' keyword. Note that in the parser we still parse data constructors as type
 constructors. As such, they still end up in the type constructor namespace until after renaming
 when we resolve the proper namespace for each exported child.
 */
qual_type_con_op: // See Note [%shift: qtyconop -> qtyconsym]
	qual_type_con_symbol /*shift  */
	| '`' qualified_type_con '`';

type_con_op: type_con_symbol | '`' type_con '`';

qualified_type_con: qualifier? type_con;

type_con: UpperName;

qual_type_con_symbol: (
		qualifier? (ConstructorSymbol | VarSymbol)
	)
	| type_con_symbol;

type_con_symbol: ConstructorSymbol | VarSymbol | '-' | '.';

// An "ordinary" unqualified tycon. See `oqtycon` for the qualified version. These can appear in
// `ANN type` declarations (#19374).
ordinary_type_con: type_con | '(' type_con_symbol ')';

//---------------------------------------------------------------------------
// Operators

op: var_op | con_op | '->';
//- used in infix decls

var_op: var_symbol | '`' var_id '`';

qualified_op: qualified_var_op | qualified_con_op | hole_op;
//- used in sections

qopm: qvaropm | qualified_con_op | hole_op;
//- used in sections

// used in sections
hole_op: '`' '_' '`';

qualified_var_op:
	qualified_var_symbol
	| '`' qualified_var_id '`';

qvaropm: qvarsym_no_minus | '`' qualified_var_id '`';

//---------------------------------------------------------------------------
// Type variables

type_var: type_var_id;

type_var_op: '`' type_var_id '`';

type_var_id:
	LowerName
	| special_id
	| 'unsafe'
	| 'safe'
	| 'interruptible';

//---------------------------------------------------------------------------
// Variables

var: var_id | '(' var_symbol ')';
qualified_var:
	qualified_var_id
	| '(' var_symbol ')'
	| '(' qvarsym1 ')';

field: var_id;

var_id:
	LowerName
	| special_id
	| 'unsafe'
	| 'safe'
	| 'interruptible'
	| 'forall'
	| 'family'
	| 'role';

qualified_var_id: qualifier? var_id;

qualified_var_symbol: var_symbol | qvarsym1;

qvarsym_no_minus: varsym_no_minus | qvarsym1;

qvarsym1: qualifier? VarSymbol;

var_symbol: varsym_no_minus | '-';

varsym_no_minus: //- varsym not including '-'
	VarSymbol
	| special_symbol;

// These special_ids are treated as keywords in various places, but as ordinary ids elsewhere.
// 'special_id' collects all these except 'unsafe', 'interruptible', 'forall', 'family', 'role',
// 'stock', and 'anyclass', whose treatment differs depending on context
special_id:
	'as'
	| 'qualified'
	| 'hiding'
	| 'export'
	| 'label'
	| 'dynamic'
	| 'stdcall'
	| 'ccall'
	| 'capi'
	| 'prim'
	| 'javascript'
	| 'group' /*shift */
	| 'stock'
	| 'anyclass'
	| 'via'
	| 'unit'
	| 'dependency'
	| 'signature';

special_symbol: '.' | '*' | '::';

//---------------------------------------------------------------------------
// Data constructors

constructor_id: UpperName;
qualified_constructor_id: qualifier? constructor_id;

qualified_constructor_symbol: qualifier? constructor_symbol;

constructor_symbol: ConstructorSymbol | ':';

literal:
	Char
	| String
	| PrimInteger
	| PrimWord
	| PrimChar
	| PrimString
	| PrimFloat
	| PrimDouble;

//---------------------------------------------------------------------------
// Miscellaneous (mostly renamings)

qualifier: module_path '.';
