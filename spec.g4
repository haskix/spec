// SPDX-License-Identifier: MIT

grammar Haskix;

tokens {
	TightInfixAt,
	PrefixMinus,
	PrefixProj /*-- RecordDotSyntax*/,
	TightInfixProj /*-- RecordDotSyntax*/,
	PrefixAt,

	LowerName,
	UpperName,
	VarSymbol,
	ConstructorSymbol,

	// literal
	Char,
	String,
	Integer,
	Rational,

	PrefixDollar
}

// -- Exported parsers %name parseModuleNoHaddock module %name parseSignature signature %name
// parseImport importdecl %name parseStatement e_stmt %name parseDeclaration topdecl %name
// parseExpression exp %name parsePattern pat %name parseTypeSignature sigdecl %name parseStmt
// maybe_stmt %name parseIdentifier identifier %name parseType ktype %name parseBackpack backpack
// %partial parseHeader header

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

module_decl: 'module' module_id modwarning? mod_body ';';

modwarning:
	'{-# DEPRECATED' strings '#-}'
	| '{-# WARNING' strings '#-}';

mod_body: 'where'? '{' top_decl* '}';

//---------------------------------------------------------------------------
// Import Declarations

fixity: infix Integer?;
rename_spec:
	qualified_var 'as' (var | fixity var_op)
	| o_qual_type_con_no_var_con 'as' (
		type_con
		| fixity type_con_op
	)
	| 'type' ordinary_qual_type_con 'as' (
		type_con
		| fixity type_con_op
	);

import_decl: 'import' module_id ('as' module_id)? ';';

open_decl:
	'open' module_path ('.' import_tree | rename_spec)? ';';

open_import_decl:
	'open' 'import' module_id (
		'using' '{' (import_tree ';')* '}'
	)? ';';

import_tree:
	'using' '{' (import_tree ';')* '}'
	| (module_id | 'super') ('.' import_tree)?
	| 'self'
	| var
	| o_qual_type_con_no_var_con
	| 'type' ordinary_qual_type_con
	| rename_spec;

// -------------------------------------------------------------------------- Visibility
// declarations

visibility:
	'public' (
		'(' ('flake' | 'self' | 'super' | 'in' module_path)
	);

vis_header: visibility 'where'?;

//---------------------------------------------------------------------------
// Fixity Declarations

infix: 'infix' | 'infixl' | 'infixr';

ops: op (',' op)*;

fixity_decl: infix Integer? ops ';';
//---------------------------------------------------------------------------
// Top-Level Declarations

top_decl:
	visibility? module_decl
	| visibility? open_decl
	| visibility? import_decl
	| visibility? open_import_decl
	| visibility? class_decl
	| visibility? type_top_decl
	| instance_decl
	| '{-# DEPRECATED' deprecation+ '#-}' ';'
	| '{-# WARNING' warning+ '#-}' ';'
	| decl_no_th
	| attribute* vis_header '{' top_decl* '}' ';';

class_decl:
	attribute* 'class' type_class_header 'where'? '{' (
		decl
		| 'default' infix_exp ':' sig_type ';'
	)* '}' ';';

type_top_decl: // ordinary type synonyms
	attribute* 'type' type '=' forall_type_with_kind ';'
	// Note ktype, not sigtype, on the right of '=' We allow an explicit for-all but we don't insert
	// one in type Foo a = (b,b) Instead we just say b is out of scope
	| attribute* data_or_newtype type_class_header kind_sig? (
		constrs
		| record
	) deriving* ';';

instance_decl:
	'instance' instance_type ('where'? '{' decl* '}')? ';';

data_or_newtype: 'data' | 'newtype';

// Family result/return kind signatures

kind_sig: ':' kind;

// tycl_hdr parses the header of a class or data type decl, which takes the form T a b Eq a => T a
// (Eq a, Ord b) => T a b T Int [a] -- for associated types Rather a lot of inlining here, else we
// get reduce/reduce errors
type_class_header: (context '=>')? type;

//---------------------------------------------------------------------------
// Datatype declarations

// We allow the following forms: C :: Eq a => a -> T a C :: forall a. Eq a => !a -> T a D { x,y :: a
// } :: T a forall a. Eq a => D { x,y :: a } :: T a

constrs:
	'where'? '{' (
		constructor
		| vis_header '{' constructor* '}' ';'
	)* '}';

constructor:
	'|' attribute* visibility? forall? (context '=>')? constr_stuff ';';

forall: 'forall' type_var_binder+ '.';

record: 'where'? record_type;

constr_stuff: infix_type;

//---------------------------------------------------------------------------
// deriving

deriving: attribute* 'deriving' deriv_clause_types;

deriv_clause_types:
	qualified_type_con
	| '(' ')'
	| '(' deriv_types ')';

qvarcon: qualified_var | qualified_con;

//---------------------------------------------------------------------------
// Nested declarations

// Binding groups other than those of class and instance declarations

binds:
	// May have implicit parameters No type declarations:
	'{' decl+ '}';

where_binds:
	// May have implicit parameters No type declarations:
	'where' binds;

//---------------------------------------------------------------------------
// Warnings and deprecations (c.f. rules)

// SUP: TEMPORARY HACK, not checking for `module Foo'
warning: name_list strings ';';

// SUP: TEMPORARY HACK, not checking for `module Foo'
deprecation: name_list strings ';';

strings: String | '[' (String (',' String)*)? ']';

//---------------------------------------------------------------------------
// Type signatures

sig: ':' forall_type;

opt_tyconsig: ( ':' general_type_con)?;

// Like ktype, but for types that obey the forall-or-nothing rule. 
sig_type_with_kind: sig_type | forall_type ':' kind;

// Like ctype, but for types that obey the forall-or-nothing rule. 
sig_type: forall_type;

sig_vars: var (',' var)*;

//---------------------------------------------------------------------------
// Types

forall_telescope: 'forall' type_var_binder+ ('.' | '->');

forall_type_with_kind: forall_type (':' kind)?;

forall_type:
	forall_telescope forall_type
	| context '=>' forall_type
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

type: b_type /*shift*/;

b_type: infix_type;

infix_type:
	type_apply /*%shift*/
	| type_apply type_op infix_type;

type_apply:
	arg_type
	| type_op
	| type_apply type_arg
	| type_apply PrefixAt arg_type;

type_arg: arg_type;

type_op: qual_type_con_op | type_var_op;

arg_type:
	n_unit_general_type_con //- Not including unit tuples
	| type_var /*%shift*/ //- (See Note [Unit tuples])
	| '*'
	| 'with'? record_type
	// Constructor sigs only
	| '(' ')'
	| '(' forall_type_with_kind ',' comma_types1 ')'
	| '[' forall_type_with_kind ']'
	| '(' forall_type_with_kind ')'
	| '_';

record_type:
	'{' (field_type | vis_header '{' field_type* '}' ';')* '}';

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

decl_no_th: sig_decl | attribute* infix_exp sig? rhs ';';

decl: decl_no_th;

rhs: ('=' exp | gdrh+) where_binds?;

gdrh: '|' guard_quals '=' exp;

sig_decl:
	// See Note [Declaration/signature overlap] for why we need infixexp here
	infix_exp ':' sig_type ';'
	| var ',' sig_vars ':' sig_type ';'
	| fixity_decl
	| '{-# COMPLETE' con_list opt_tyconsig '#-}' ';'
	// This rule is for both INLINE and INLINABLE pragmas
	| '{-# BUILTIN' qvarcon '#-}' ';'
	// A minimal complete definition
	| '{-# MINIMAL' name_boolformula? '#-}' ';';

//---------------------------------------------------------------------------
// Expressions

exp: infix_exp ':' forall_type | infix_exp /*shift*/;

infix_exp: exp10 | infix_exp qualified_op exp10;

exp10: '-'? fun_exp;

fun_exp: fun_exp arg_exp | fun_exp PrefixAt arg_type | arg_exp;

arg_exp:
	qualified_var TightInfixAt arg_exp
	| PrefixMinus arg_exp
	| '\\' arg_pattern* '->' exp
	| 'let' binds 'in' exp
	| 'if' exp 'then' exp 'else' exp
	| 'if' '{' guard_pattern+ '}'
	| 'case' exp 'of'? alts_list
	| arg_exp1;

arg_exp1:
	arg_exp1 '{' field_binds '}'
	| arg_exp1 TightInfixProj field
	| arg_exp2;

arg_exp2:
	qualified_var
	| qualified_con
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
	| '[' list ']'
	| '_'
	// Template Haskell Extension
	| splice_untyped;

projection: projection TightInfixProj field | PrefixProj field;

splice_untyped: PrefixDollar '(' 'includeStr' String ')';

//---------------------------------------------------------------------------
// Tuple expressions

// "texp" is short for tuple expressions: things that can appear unparenthesized as long as they're
// inside parens or delimited by commas
tuple_exp: exp;

// Always at least one comma or bar. Though this can parse just commas (without any expressions), it
// won't in practice, because (,,,) is parsed as a name. See Note [ExplicitTuple] in GHC.Hs.Expr.
tuple_exprs: tuple_exp? commas_tup_tail;

// Always starts with commas; always follows an expr
commas_tup_tail: ','+ tup_tail?;

// Always follows a comma
tup_tail: tuple_exp commas_tup_tail?;

//---------------------------------------------------------------------------
// List expressions

list:
	tuple_exp
	| lexps
	| tuple_exp '..' exp
	| tuple_exp ',' exp '..' exp;

lexps: (lexps | tuple_exp) ',' tuple_exp;

//---------------------------------------------------------------------------
// Guards

guard_quals: qual (',' qual)+;

//---------------------------------------------------------------------------
// Case alternatives

alts_list:
	'{' (
		pattern /* <- multiway if is not allowed  */ alt_rhs ';'
	)* '}';

alt_rhs:
	'->' exp where_binds?
	| guard_pattern+ where_binds?;

guard_pattern: '|' guard_quals '->' exp ';';

//--------------------------------------------------------------------------------
// Patterns

// 'pat' recognises a pattern, including one with a bang at the top e.g. "!x" or "!(x,y)" or "C a b"
// etc Bangs inside are parsed as infix operator applications, so that we parse them right when
// bang-patterns are off
pattern: exp;

bind_pattern: exp;

arg_pattern: arg_exp;

//---------------------------------------------------------------------------
// Statement sequences

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
// Attributes

attribute: '{-# ATTRIB' exp '#-}';

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
	| '(' ','+ ')';

// See Note [Empty lists] in GHC.Hs.Expr
sysd_con: sysd_con_nolist | '[' ']';

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
general_type_con: n_unit_general_type_con | '(' ')';

/** A "general" qualified tycon, excluding unit tuples */
n_unit_general_type_con:
	ordinary_qual_type_con
	| '(' ','+ ')'
	| '(' '->' ')'
	| '[' ']';

ordinary_qual_type_con:
	qualified_type_con
	| '(' qual_type_con_symbol ')'; // These can appear in export lists

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

//---------------------------------------------------------------------------
// Operators

op: var_op | con_op | '->'; //- used in infix decls

var_op: var_symbol | '`' var_id '`';

qualified_op:
	qualified_var_op
	| qualified_con_op
	| hole_op; //- used in sections

qopm: qvaropm | qualified_con_op | hole_op; //- used in sections

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

literal: Char | String;

//---------------------------------------------------------------------------
// Miscellaneous (mostly renamings)

qualifier: module_path '.';
