// SPDX-License-Identifier: MIT
// --------------------------------------------------------------------------- (c) The University of
// Glasgow 1997-2003 - The GHC grammar.
// 
// Author(s): Simon Marlow, Sven Panne 1997, 1998, 1999
// ---------------------------------------------------------------------------

grammar ghc;

// %expect 0 -- shift/reduce conflicts

/* Note [shift/reduce conflicts]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 The 'happy' tool turns this
 grammar into an efficient parser that follows the
 shift-reduce parsing model. There's a parse
 stack that contains items parsed so
 far (both terminals and non-terminals). Every next token
 produced by the lexer
 results in one of two actions:
 SHIFT: push the token onto the parse stack
 REDUCE: pop a few items off the parse stack and combine them
 with a function (reduction rule)
 However, sometimes it's unclear which of the two actions to take.
 Consider this code example:
 if
 x then y else f z
 There are two ways to parse it:
 (if x then y else f) z
 if x then y else (f z)
 How is this determined? At some point, the parser gets to the following state:
 parse stack: 'if'
 exp 'then' exp 'else' "f"
 next token: "z"
 Scenario A (simplified):
 1. REDUCE, parse stack: 'if'
 exp 'then' exp 'else' exp
 next token: "z"
 (Note that "f" reduced to exp here)
 2. REDUCE, parse
 stack: exp
 next token: "z"
 3. SHIFT, parse stack: exp "z"
 next token: ...
 4. REDUCE, parse
 stack: exp
 next token: ...
 This way we get: (if x then y else f) z
 Scenario B (simplified):
 1.
 SHIFT, parse stack: 'if' exp 'then' exp 'else' "f" "z"
 next token: ...
 2. REDUCE, parse stack:
 'if' exp 'then' exp 'else' exp
 next token: ...
 3. REDUCE, parse stack: exp
 next token: ...
 This
 way we get: if x then y else (f z)
 The end result is determined by the chosen action. When
 Happy
 detects this, it
 reports a shift/reduce conflict. At the top of the file, we have the
 following
 directive:
 %expect 0
 It means that we expect no unresolved shift/reduce conflicts in
 this
 grammar.
 If you modify the grammar and get shift/reduce conflicts, follow the steps
 below
 to
 resolve them.
 STEP ONE
 is to figure out what causes the conflict.
 That's where the -i flag
 comes
 in handy:
 happy -agc --strict compiler/GHC/Parser.y -idetailed-info
 By analysing the
 output of
 this command, in a new file `detailed-info`, you
 can figure out which reduction rule
 causes the
 issue. At the top of the
 generated report, you will see a line like this:
 state 147
 contains 67
 shift/reduce conflicts.
 Scroll down to section State 147 (in your case it could be a
 different
 state). The start of the section lists the reduction rules that can fire
 and shows
 their context:
 exp10 -> fexp . (rule 492)
 fexp -> fexp . aexp (rule 498)
 fexp -> fexp .
 PREFIX_AT atype (rule
 499)
 And then, for every token, it tells you the parsing action:
 ']'
 reduce using rule 492
 '::'
 reduce using rule 492
 '(' shift, and enter state 178
 QVARID shift,
 and enter state 44
 DO shift,
 and enter state 182
 ...
 But if you look closer, some of these
 tokens also have another parsing
 action
 in parentheses:
 QVARID shift, and enter state 44
 (reduce using rule 492)
 That's how you
 know rule 492 is causing trouble.
 Scroll back to the top
 to see what this rule is:
 ----------------------------------
 Grammar
 ----------------------------------
 ...
 ...
 exp10 ->
 fexp (492)
 optSemi -> ';' (493)
 ...
 ...
 Hence the shift/reduce conflict is caused by this
 parser production:
 exp10 :: { ECP }
 : '-'
 fexp
 { ... }
 | fexp { ... } -- problematic rule
 STEP
 TWO
 is to mark the problematic rule with
 the
 %shift pragma. This signals to
 'happy' that any
 shift/reduce conflicts involving this rule
 must
 be resolved
 in favor of a shift. There's currently
 no dedicated pragma to resolve in
 favor
 of
 the reduce.
 STEP THREE
 is to add a dedicated Note for
 this specific conflict, as is
 done
 for
 all
 other conflicts below.
 */

/* Note [%shift: rule_activation -> {- empty -}]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 rule -> STRING . rule_activation rule_foralls infixexp '=' exp
 Example:
 {-# RULES
 "name" [0] f = rhs #-}
 Ambiguity:
 If we reduced, then we'd get an empty activation rule, and [0]
 would be
 parsed as part of the left-hand side expression.
 We shift, so [0] is parsed as an
 activation rule.
 */

/* Note [%shift: rule_foralls -> 'forall' rule_vars '.']
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 rule_foralls -> 'forall'
 rule_vars '.' . 'forall' rule_vars '.'
 rule_foralls -> 'forall' rule_vars '.' .
 Example:
 {-#
 RULES "name" forall a1. forall a2. lhs = rhs #-}
 Ambiguity:
 Same as in Note [%shift:
 rule_foralls
 -> {- empty -}]
 but for the second 'forall'.
 */

/* Note [%shift: rule_foralls -> {- empty -}]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 rule -> STRING rule_activation . rule_foralls infixexp '=' exp
 Example:
 {-# RULES
 "name" forall a1. lhs = rhs #-}
 Ambiguity:
 If we reduced, then we would get an empty
 rule_foralls; the 'forall', being
 a valid term-level identifier, would be parsed as part of the
 left-hand
 side expression.
 We shift, so the 'forall' is parsed as part of rule_foralls.
 */

/* Note [%shift: type -> btype]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 context -> btype .
 type
 -> btype .
 type -> btype . '->' ctype
 type -> btype . '->.' ctype
 Example:
 a :: Maybe
 Integer
 -> Bool
 Ambiguity:
 If we reduced, we would get: (a :: Maybe Integer) -> Bool
 We shift
 to get
 this instead: a :: (Maybe Integer -> Bool)
 */

/* Note [%shift: infixtype -> ftype]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 infixtype ->
 ftype .
 infixtype -> ftype . tyop infixtype
 ftype -> ftype . tyarg
 ftype -> ftype . PREFIX_AT
 tyarg
 Example:
 a :: Maybe Integer
 Ambiguity:
 If we reduced, we would get: (a :: Maybe) Integer
 We shift to get this instead: a :: (Maybe Integer)
 */

/* Note [%shift: atype -> tyvar]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 atype -> tyvar .
 tv_bndr_no_braces -> '(' tyvar . '::' kind ')'
 Example:
 class C a where type D a = (a :: Type
 ...
 Ambiguity:
 If we reduced, we could specify a default for an associated type like this:
 class
 C a where type D a
 type D a = (a :: Type)
 But we shift in order to allow injectivity
 signatures
 like this:
 class C a where type D a = (r :: Type) | r -> a
 */

/* Note [%shift: exp -> infixexp]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 exp -> infixexp .
 '::' sigtype
 exp -> infixexp . '-<' exp
 exp -> infixexp . '>-' exp
 exp -> infixexp . '-<<' exp
 exp -> infixexp . '>>-' exp
 exp -> infixexp .
 infixexp -> infixexp . qop exp10p
 Examples:
 1)
 if
 x then y else z -< e
 2) if x then y else z :: T
 3) if x then y else z + 1 -- (NB: '+' is in
 VARSYM)
 Ambiguity:
 If we reduced, we would get:
 1) (if x then y else z) -< e
 2) (if x then y
 else z) :: T
 3) (if x then y else z) + 1
 We shift to get this instead:
 1) if x then y else (z
 -<
 e)
 2) if x then y else (z :: T)
 3) if x then y else (z + 1)
 */

/* Note [%shift: exp10 -> '-' fexp]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 exp10 -> '-'
 fexp .
 fexp -> fexp . aexp
 fexp -> fexp . PREFIX_AT atype
 Examples & Ambiguity:
 Same as in
 Note
 [%shift: exp10 -> fexp],
 but with a '-' in front.
 */

/* Note [%shift: exp10 -> fexp]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 exp10 -> fexp .
 fexp
 ->
 fexp . aexp
 fexp -> fexp . PREFIX_AT atype
 Examples:
 1) if x then y else f z
 2) if x then
 y
 else f @z
 Ambiguity:
 If we reduced, we would get:
 1) (if x then y else f) z
 2) (if x then y
 else f) @z
 We shift to get this instead:
 1) if x then y else (f z)
 2) if x then y else (f @z)
 */

/* Note [%shift: aexp2 -> ipvar]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 aexp2 -> ipvar .
 dbind -> ipvar . '=' exp
 Example:
 let ?x = ...
 Ambiguity:
 If we reduced, ?x would be parsed as
 the LHS of a normal binding,
 eventually producing an error.
 We shift, so it is parsed as the LHS
 of an implicit binding.
 */

/* Note [%shift: aexp2 -> TH_TY_QUOTE]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 aexp2 ->
 TH_TY_QUOTE . tyvar
 aexp2 -> TH_TY_QUOTE . gtycon
 aexp2 -> TH_TY_QUOTE .
 Examples:
 1) x = ''
 2) x = ''a
 3) x = ''T
 Ambiguity:
 If we reduced, the '' would result in reportEmptyDoubleQuotes
 even when
 followed by a type variable or a type constructor. But the only reason
 this reduction
 rule exists is to improve error messages.
 Naturally, we shift instead, so that ''a and ''T work
 as
 expected.
 */

/* Note [%shift: tup_tail -> {- empty -}]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 tup_exprs -> commas . tup_tail
 sysdcon_nolist -> '(' commas . ')'
 sysdcon_nolist -> '(#' commas
 .
 '#)'
 commas -> commas . ','
 Example:
 (,,)
 Ambiguity:
 A tuple section with no components is
 indistinguishable from the Haskell98
 data constructor for a tuple.
 If we reduced, (,,) would be
 parsed as a tuple section.
 We shift, so (,,) is parsed as a data constructor.
 This is preferable
 because we want to accept (,,) without -XTupleSections.
 See also Note [ExplicitTuple] in
 GHC.Hs.Expr.
 */

/* Note [%shift: qtyconop -> qtyconsym]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 oqtycon
 -> '(' qtyconsym . ')'
 qtyconop -> qtyconsym .
 Example:
 foo :: (:%)
 Ambiguity:
 If we reduced,
 (:%) would be parsed as a parenthehsized infix type
 expression without arguments, resulting in
 the
 'failOpFewArgs' error.
 We shift, so it is parsed as a type constructor.
 */

/* Note [%shift: special_id -> 'group']
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 transformqual -> 'then' 'group' . 'using' exp
 transformqual -> 'then' 'group' . 'by' exp 'using'
 exp
 special_id -> 'group' .
 Example:
 [ ... | then group by dept using groupWith
 , then take 5
 ]
 Ambiguity:
 If we reduced, 'group' would be parsed as a term-level identifier, just as
 'take'
 in the other clause.
 We shift, so it is parsed as part of the 'group by' clause introduced by
 the
 -XTransformListComp extension.
 */

/* Note [%shift: activation -> {- empty -}]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Context:
 sigdecl -> '{-# INLINE' . activation qvarcon '#-}'
 activation -> {- empty -}
 activation ->
 explicit_activation
 Example:
 {-# INLINE [0] Something #-}
 Ambiguity:
 We don't know whether the
 '[' is the start of the activation or the beginning
 of the [] data constructor.
 We parse this as
 having '[0]' activation for inlining 'Something', rather than
 empty activation and inlining '[0]
 Something'.
 */

/* Note [Parser API Annotations]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 A lot of the productions are
 now
 cluttered with calls to
 aa,am,acs,acsA etc.
 These are helper functions to make sure that
 the
 locations of the
 various keywords such as do / let / in are captured for use by tools
 that
 want
 to do source to source conversions, such as refactorers or
 structured editors.
 The helper
 functions are defined at the bottom of this file.
 See
 https://gitlab.haskell.org/ghc/ghc/wikis/api-annotations and
 https://gitlab.haskell.org/ghc/ghc/wikis/ghc-ast-annotations
 for some background.
 */

/* Note [Parsing lists]
 ~~~~~~~~~~~~~~~~~~~~~~~
 You might be wondering why we spend so much
 effort
 encoding our lists this
 way:
 importdecls
 : importdecls ';' importdecl
 | importdecls
 ';'
 |
 importdecl
 | {- empty -}
 This might seem like an awfully roundabout way to declare a
 list; plus,
 to add
 insult to injury you have to reverse the results at the end. The answer is
 that
 left
 recursion prevents us from running out of stack space when parsing long
 sequences.
 See:
 https://www.haskell.org/happy/doc/html/sec-sequences.html for
 more guidance.
 By
 adding/removing
 branches, you can affect what lists are accepted. Here
 are the most common
 patterns, rewritten as
 regular expressions for clarity:
 -- Equivalent to: ';'* (x ';'+)* x? (can
 be empty, permits
 leading/trailing semis)
 xs : xs ';' x
 | xs ';'
 | x
 | {- empty -}
 --
 Equivalent to x (';' x)*
 ';'* (non-empty, permits trailing semis)
 xs : xs ';' x
 | xs ';'
 | x
 -- Equivalent to ';'* alts
 (';' alts)* ';'* (non-empty, permits leading/trailing semis)
 alts :
 alts1
 | ';' alts
 alts1 :
 alts1 ';' alt
 | alts1 ';'
 | alt
 -- Equivalent to x (',' x)+
 (non-empty, no trailing semis)
 xs :
 x
 | x ',' xs
 */

tokens {
	TIGHT_INFIX_AT /*{ L _ ITat }*/,
	PREFIX_TILDE /*{ L _ ITtilde }*/,
	PREFIX_BANG /*{ L _ ITbang }*/,
	PREFIX_MINUS /*{ L _ ITprefixminus }*/,
	PREFIX_PROJ /*{ L _ (ITproj True) }               -- RecordDotSyntax*/,
	TIGHT_INFIX_PROJ /*{ L _ (ITproj False) }            -- RecordDotSyntax*/,
	PREFIX_AT /*{ L _ ITtypeApp }*/,
	PREFIX_PERCENT /*{ L _ ITpercent }                   -- for linear types*/,
	vocurly /*{ L _ ITvocurly } -- virtual open curly (from layout)*/,
	vccurly /*{ L _ ITvccurly } -- virtual close curly (from layout)*/,
	SIMPLEQUOTE /*{ L _ ITsimpleQuote      }     -- 'x*/,
	VARID /*{ L _ (ITvarid    _) }          -- identifiers*/,
	CONID /*{ L _ (ITconid    _) }*/,
	VARSYM /*{ L _ (ITvarsym   _) }*/,
	CONSYM /*{ L _ (ITconsym   _) }*/,
	QVARID /*{ L _ (ITqvarid   _) }*/,
	QCONID /*{ L _ (ITqconid   _) }*/,
	QVARSYM /*{ L _ (ITqvarsym  _) }*/,
	QCONSYM /*{ L _ (ITqconsym  _) }*/,
	DO /*{ L _ (ITdo  _) }*/,
	MDO /*{ L _ (ITmdo _) }*/,
	IPDUPVARID /*{ L _ (ITdupipvarid   _) }              -- GHC extension*/,
	LABELVARID /*{ L _ (ITlabelvarid   _) }*/,
	CHAR /*{ L _ (ITchar   _ _) }*/,
	STRING /*{ L _ (ITstring _ _) }*/,
	INTEGER /*{ L _ (ITinteger _) }*/,
	RATIONAL /*{ L _ (ITrational _) }*/,
	PRIMCHAR /*{ L _ (ITprimchar   _ _) }*/,
	PRIMSTRING /*{ L _ (ITprimstring _ _) }*/,
	PRIMINTEGER /*{ L _ (ITprimint    _ _) }*/,
	PRIMWORD /*{ L _ (ITprimword   _ _) }*/,
	PRIMFLOAT /*{ L _ (ITprimfloat  _) }*/,
	PRIMDOUBLE /*{ L _ (ITprimdouble _) }*/,
	PREFIX_DOLLAR /*{ L _ ITdollar }*/,
	PREFIX_DOLLAR_DOLLAR /*{ L _ ITdollardollar }*/,
	TH_TY_QUOTE /*{ L _ ITtyQuote       }      -- ''T*/,
	TH_QUASIQUOTE /*{ L _ (ITquasiQuote _) }*/,
	TH_QQUASIQUOTE /*{ L _ (ITqQuasiQuote _) }*/
}

// %monad { P } { >>= } { return } %lexer { (lexer True) } { L _ ITeof } -- Replace 'lexer' above
// with 'lexerDbg' -- to dump the tokens fed to the parser. %tokentype { (Located Token) }

// -- Exported parsers %name parseModuleNoHaddock module %name parseSignature signature %name
// parseImport importdecl %name parseStatement e_stmt %name parseDeclaration topdecl %name
// parseExpression exp %name parsePattern pat %name parseTypeSignature sigdecl %name parseStmt
// maybe_stmt %name parseIdentifier identifier %name parseType ktype %name parseBackpack backpack
// %partial parseHeader header

//---------------------------------------------------------------------------
// Identifiers; one of the entry points
identifier: qvar | qcon | qvarop | qconop | '(' '->' ')' | '->';

//---------------------------------------------------------------------------
// Backpack stuff

backpack: implicit_top units close | '{' units '}';

units: units ';' unit | units ';' | unit;

unit: 'unit' pkgname 'where' unitbody;

unitid: pkgname | pkgname '[' msubsts ']';

msubsts: msubsts ',' msubst | msubsts ',' | msubst;

msubst: modid '=' moduleid | modid VARSYM modid VARSYM;

moduleid: VARSYM modid VARSYM | unitid ':' modid;

pkgname: STRING | litpkgname;

litpkgname_segment: VARID | CONID | special_id;

// Parse a minus sign regardless of whether -XLexicalNegation is turned on or off. See Note [Minus
// tokens] in GHC.Parser.Lexer
HYPHEN: '-' | PREFIX_MINUS | VARSYM;

litpkgname:
	litpkgname_segment
	// a bit of a hack, means p - b is parsed same as p-b, enough for now.
	| litpkgname_segment HYPHEN litpkgname;

mayberns: | '(' rns ')';

rns: rns ',' rn | rns ',' | rn;

rn: modid 'as' modid | modid;

unitbody: '{' unitdecls '}' | vocurly unitdecls close;

unitdecls: unitdecls ';' unitdecl | unitdecls ';' | unitdecl;

unitdecl:
	'module' maybe_src modid maybemodwarning maybeexports 'where' body
	// XXX not accurate
	| 'signature' modid maybemodwarning maybeexports 'where' body
	| 'dependency' unitid mayberns
	| 'dependency' 'signature' unitid;

//---------------------------------------------------------------------------
// Module Header

// The place for module deprecation is really too restrictive, but if it was allowed at its natural
// place just before 'module', we get an ugly s/r conflict with the second alternative. Another
// solution would be the introduction of a new pragma DEPRECATED_MODULE, but this is not very nice,
// either, and DEPRECATED is only expected to be used by people who really know what they are doing.
// :-)

signature:
	'signature' modid maybemodwarning maybeexports 'where' body;

module:
	'module' modid maybemodwarning maybeexports 'where' body
	| body2;

missing_module_keyword:;

implicit_top:;

maybemodwarning:
	'{-# DEPRECATED' strings '#-}'
	| '{-# WARNING' strings '#-}'
	|;

body: '{' top '}' | vocurly top close;

body2: '{' top '}' | missing_module_keyword top close;

top: semis top1;

top1:
	importdecls_semi topdecls_cs_semi
	| importdecls_semi topdecls_cs
	| importdecls;

//---------------------------------------------------------------------------
// Module declaration & imports only

header:
	'module' modid maybemodwarning maybeexports 'where' header_body
	| 'signature' modid maybemodwarning maybeexports 'where' header_body
	| header_body2;

header_body: '{' header_top | vocurly header_top;

header_body2:
	'{' header_top
	| missing_module_keyword header_top;

header_top: semis header_top_importdecls;

header_top_importdecls: importdecls_semi | importdecls;

//---------------------------------------------------------------------------
// The Export List

maybeexports: '(' exportlist ')' |;

exportlist:
	exportlist1
	|

	// trailing comma:
	| exportlist1 ','
	| ',';

exportlist1: exportlist1 ',' export | export;

// No longer allow things like [] and (,,,) to be exported They are built in syntax, always
// available
export:
	qcname_ext export_subspec
	| 'module' modid
	| 'pattern' qcon;

export_subspec: | '(' qcnames ')';

qcnames: | qcnames1;

qcnames1:
	qcnames1 ',' qcname_ext_w_wildcard

	// Annotations re-added in mkImpExpSubSpec
	| qcname_ext_w_wildcard;

// Variable, data constructor or wildcard or tagged type constructor
qcname_ext_w_wildcard: qcname_ext | '..';

qcname_ext: qcname | 'type' oqtycon;

qcname: // Variable or type constructor
	qvar // Things which look like functions
	// Note: This includes record selectors but also (-.->), see #11432
	| oqtycon_no_varcon; //- see Note [Type constructors in export list]

//---------------------------------------------------------------------------
// Import Declarations

// importdecls and topdecls must contain at least one declaration; top handles the fact that these
// may be optional.

// One or more semicolons
semis1: semis1 ';' | ';';

// Zero or more semicolons
semis: semis ';' |;

// No trailing semicolons, non-empty
importdecls: importdecls_semi importdecl;

// May have trailing semicolons, can be empty
importdecls_semi: importdecls_semi importdecl semis1 |;

importdecl:
	'import' maybe_src maybe_safe optqualified maybe_pkg modid optqualified maybeas maybeimpspec;

maybe_src: '{-# SOURCE' '#-}' |;

maybe_safe: 'safe' |;

maybe_pkg: STRING |;

optqualified: 'qualified' |;

maybeas: 'as' modid |;

maybeimpspec: impspec |;

impspec: '(' exportlist ')' | 'hiding' '(' exportlist ')';

//---------------------------------------------------------------------------
// Fixity Declarations

prec: | INTEGER;

infix: 'infix' | 'infixl' | 'infixr';

ops: ops ',' op | op;

//---------------------------------------------------------------------------
// Top-Level Declarations

// No trailing semicolons, non-empty
topdecls: topdecls_semi topdecl;

// May have trailing semicolons, can be empty
topdecls_semi: topdecls_semi topdecl semis1 |;

//---------------------------------------------------------------------------
// Each topdecl accumulates prior comments No trailing semicolons, non-empty
topdecls_cs: topdecls_cs_semi topdecl_cs;

// May have trailing semicolons, can be empty
topdecls_cs_semi: topdecls_cs_semi topdecl_cs semis1 |;

// Each topdecl accumulates prior comments
topdecl_cs: topdecl;

//---------------------------------------------------------------------------
topdecl:
	cl_decl
	| ty_decl
	| standalone_kind_sig
	| inst_decl
	| stand_alone_deriving
	| role_annot
	| 'default' '(' comma_types0 ')'
	| 'foreign' fdecl
	| '{-# DEPRECATED' deprecations '#-}'
	| '{-# WARNING' warnings '#-}'
	| '{-# RULES' rules '#-}'
	| annotation
	| decl_no_th

	// Template Haskell Extension The $(..) form is one possible form of infixexp but we treat an
	// arbitrary expression just as if it had a $(..) wrapped around it
	| infixexp;

// Type classes
cl_decl: 'class' tycl_hdr fds where_cls;

// Type declarations (toplevel)
ty_decl: // ordinary type synonyms
	'type' type '=' ktype
	// Note ktype, not sigtype, on the right of '=' We allow an explicit for-all but we don't insert
	// one in type Foo a = (b,b) Instead we just say b is out of scope
	// 
	// Note the use of type for the head; this allows infix type constructors to be declared

	// type family declarations
	| 'type' 'family' type opt_tyfam_kind_sig opt_injective_info where_type_family
	// Note the use of type for the head; this allows infix type constructors to be declared

	// ordinary data type or newtype declaration
	| data_or_newtype capi_ctype tycl_hdr constrs maybe_derivings
	// We need the location on tycl_hdr in case constrs and deriving are both empty

	// ordinary GADT declaration
	| data_or_newtype capi_ctype tycl_hdr opt_kind_sig gadt_constrlist maybe_derivings
	// We need the location on tycl_hdr in case constrs and deriving are both empty

	// data/newtype family
	| 'data' 'family' type opt_datafam_kind_sig;

// standalone kind signature
standalone_kind_sig: 'type' sks_vars '::' sigktype;

// See also: sig_vars
sks_vars: sks_vars ',' oqtycon;

inst_decl:
	'instance' overlap_pragma inst_type where_inst

	// type instance declarations
	| 'type' 'instance' ty_fam_inst_eqn
	// data/newtype instance declaration
	| data_or_newtype 'instance' capi_ctype datafam_inst_hdr constrs maybe_derivings

	// GADT instance declaration
	| data_or_newtype 'instance' capi_ctype datafam_inst_hdr opt_kind_sig gadt_constrlist
		maybe_derivings;

overlap_pragma:
	'{-# OVERLAPPABLE' '#-}'
	| '{-# OVERLAPPING' '#-}'
	| '{-# OVERLAPS' '#-}'
	| '{-# INCOHERENT' '#-}'
	|;

deriv_strategy_no_via: 'stock' | 'anyclass' | 'newtype';

deriv_strategy_via: 'via' sigktype;

deriv_standalone_strategy:
	'stock'
	| 'anyclass'
	| 'newtype'
	| deriv_strategy_via
	|;

// Injective type families

opt_injective_info: | '|' injectivity_cond;

injectivity_cond: tyvarid '->' inj_varids;

inj_varids: inj_varids tyvarid | tyvarid;

// Closed type families

where_type_family: | 'where' ty_fam_inst_eqn_list;

ty_fam_inst_eqn_list:
	'{' ty_fam_inst_eqns '}'
	| vocurly ty_fam_inst_eqns close
	| '{' '..' '}'
	| vocurly '..' close;

ty_fam_inst_eqns:
	ty_fam_inst_eqns ';' ty_fam_inst_eqn
	| ty_fam_inst_eqns ';'
	| ty_fam_inst_eqn
	|;

ty_fam_inst_eqn:
	'forall' tv_bndrs '.' type '=' ktype
	| type '=' ktype;
// Note the use of type for the head; this allows infix type constructors and type patterns

// Associated type family declarations
// 
// * They have a different syntax than on the toplevel (no family special identifier).
// 
// * They also need to be separate from instances; otherwise, data family declarations without a
// kind signature cause parsing conflicts with empty data declarations.

at_decl_cls: //- data family declarations, with optional 'family' keyword
	'data' opt_family type opt_datafam_kind_sig

	// type family declarations, with optional 'family' keyword (can't use opt_instance because you
	// get shift/reduce errors
	| 'type' type opt_at_kind_inj_sig
	| 'type' 'family' type opt_at_kind_inj_sig
	// default type instances, with optional 'instance' keyword
	| 'type' ty_fam_inst_eqn
	| 'type' 'instance' ty_fam_inst_eqn;

opt_family: | 'family';

opt_instance: | 'instance';

// Associated type instances
at_decl_inst: // type instance declarations, with optional 'instance' keyword
	'type' opt_instance ty_fam_inst_eqn
	// Note the use of type for the head; this allows infix type constructors and type patterns

	// data/newtype instance declaration, with optional 'instance' keyword
	| data_or_newtype opt_instance capi_ctype datafam_inst_hdr constrs maybe_derivings

	// GADT instance declaration, with optional 'instance' keyword
	| data_or_newtype opt_instance capi_ctype datafam_inst_hdr opt_kind_sig gadt_constrlist
		maybe_derivings;

data_or_newtype: 'data' | 'newtype';

// Family result/return kind signatures

opt_kind_sig: | '::' kind;

opt_datafam_kind_sig: | '::' kind;

opt_tyfam_kind_sig: | '::' kind | '=' tv_bndr;

opt_at_kind_inj_sig:
	| '::' kind
	| '=' tv_bndr_no_braces '|' injectivity_cond;

// tycl_hdr parses the header of a class or data type decl, which takes the form T a b Eq a => T a
// (Eq a, Ord b) => T a b T Int [a] -- for associated types Rather a lot of inlining here, else we
// get reduce/reduce errors
tycl_hdr: context '=>' type | type;

datafam_inst_hdr:
	'forall' tv_bndrs '.' context '=>' type
	| 'forall' tv_bndrs '.' type
	| context '=>' type
	| type;

capi_ctype:
	'{-# CTYPE' STRING STRING '#-}'
	| '{-# CTYPE' STRING '#-}'
	|;

//---------------------------------------------------------------------------
// Stand-alone deriving

// Glasgow extension: stand-alone deriving declarations
stand_alone_deriving:
	'deriving' deriv_standalone_strategy 'instance' overlap_pragma inst_type;

//---------------------------------------------------------------------------
// Role annotations

role_annot: 'type' 'role' oqtycon maybe_roles;

// Reversed!
maybe_roles: | roles;

roles: role | roles role;

// read it in as a varid for better error messages
role: VARID | '_';

// Pattern synonyms

// Glasgow extension: pattern synonyms
pattern_synonym_decl:
	'pattern' pattern_synonym_lhs '=' pat
	| 'pattern' pattern_synonym_lhs '<-' pat
	| 'pattern' pattern_synonym_lhs '<-' pat where_decls;

pattern_synonym_lhs:
	con vars0
	| varid conop varid
	| con '{' cvars1 '}';

vars0: | varid vars0;

cvars1: var | var ',' cvars1;

where_decls:
	'where' '{' decls '}'
	| 'where' vocurly decls close;

pattern_synonym_sig: 'pattern' con_list '::' sigtype;

qvarcon: qvar | qcon;

//---------------------------------------------------------------------------
// Nested declarations

// Declaration in class bodies

decl_cls:
	at_decl_cls
	| decl

	// A 'default' signature used with the generic-programming extension
	| 'default' infixexp '::' sigtype;

decls_cls: //- Reversed
	decls_cls ';' decl_cls
	| decls_cls ';'
	| decl_cls
	|;

decllist_cls: // Reversed
	'{' decls_cls '}'
	| vocurly decls_cls close;

// Class body

where_cls:
	// No implicit parameters May have type declarations:
	'where' decllist_cls;

// Declarations in instance bodies

decl_inst: at_decl_inst | decl;

decls_inst: //- Reversed
	decls_inst ';' decl_inst
	| decls_inst ';'
	| decl_inst
	|;

decllist_inst: // Reversed
	'{' decls_inst '}'
	| vocurly decls_inst close;

// Instance body

where_inst:
	// Reversed No implicit parameters May have type declarations:
	'where' decllist_inst
	|;

// Declarations in binding groups other than classes and instances

decls: decls ';' decl | decls ';' | decl |;

decllist: '{' decls '}' | vocurly decls close;

// Binding groups other than those of class and instance declarations

binds:
	// May have implicit parameters No type declarations:
	decllist
	| '{' dbinds '}'
	| vocurly dbinds close;

wherebinds:
	// May have implicit parameters No type declarations:
	'where' binds
	|;

//---------------------------------------------------------------------------
// Transformation Rules

rules: //- Reversed
	rules ';' rule
	| rules ';'
	| rule
	|;

rule: STRING rule_activation rule_foralls infixexp '=' exp;

// Rules can be specified to be NeverActive, unlike inline/specialize pragmas
rule_activation: // See Note [%shift: rule_activation -> {- empty -}]
	/*%shift */
	| rule_explicit_activation;

// This production is used to parse the tilde syntax in pragmas such as * {-# INLINE[~2] ... #-} *
// {-# SPECIALISE [~ 001] ... #-} * {-# RULES ... [~0] ... g #-} Note that it can be written either
// without a space [~1] (the PREFIX_TILDE case), or with a space [~ 1] (the VARSYM case). See Note
// [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
rule_activation_marker: PREFIX_TILDE | VARSYM;

rule_explicit_activation: // In brackets
	'[' INTEGER ']'
	| '[' rule_activation_marker INTEGER ']'
	| '[' rule_activation_marker ']';

rule_foralls:
	'forall' rule_vars '.' 'forall' rule_vars '.'

	// See Note [%shift: rule_foralls -> 'forall' rule_vars '.']
	| 'forall' rule_vars '.' /*%shift*/
	// See Note [%shift: rule_foralls -> {- empty -}]
	| /*%shift */;

rule_vars: rule_var rule_vars |;

rule_var: varid | '(' varid '::' ctype ')';

/* Note [Parsing explicit foralls in Rules]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We really
 want the above definition of rule_foralls to be:
 rule_foralls : 'forall' tv_bndrs '.' 'forall'
 rule_vars '.'
 | 'forall' rule_vars '.'
 | {- empty -}
 where rule_vars (term variables) can be
 named "forall", "family", or "role",
 but tv_vars (type variables) cannot be. However, such a
 definition results
 in a reduce/reduce conflict. For example, when parsing:
 > {-# RULE "name"
 forall a ... #-}
 before the '...' it is impossible to determine whether we should be in the
 first
 or second case of the above.
 This is resolved by using rule_vars (which is more general)
 for both,
 and
 ensuring that type-level quantified variables do not have the names "forall",
 "family", or
 "role" in the function 'checkRuleTyVarBndrNames' in
 GHC.Parser.PostProcess.
 Thus,
 whenever the
 definition of tyvarid (used for tv_bndrs) is changed relative
 to varid (used for
 rule_vars),
 'checkRuleTyVarBndrNames' must be updated.
 */

//---------------------------------------------------------------------------
// Warnings and deprecations (c.f. rules)

warnings: warnings ';' warning | warnings ';' | warning |;

// SUP: TEMPORARY HACK, not checking for `module Foo'
warning: namelist strings;

deprecations:
	deprecations ';' deprecation
	| deprecations ';'
	| deprecation
	|;

// SUP: TEMPORARY HACK, not checking for `module Foo'
deprecation: namelist strings;

strings: STRING | '[' stringlist ']';

stringlist: stringlist ',' STRING | STRING |;

//---------------------------------------------------------------------------
// Annotations
annotation:
	'{-# ANN' name_var aexp '#-}'
	| '{-# ANN' 'type' otycon aexp '#-}'
	| '{-# ANN' 'module' aexp '#-}';

//---------------------------------------------------------------------------
// Foreign import and export declarations

fdecl:
	'import' callconv safety fspec
	| 'import' callconv fspec
	| 'export' callconv fspec;

callconv: 'stdcall' | 'ccall' | 'capi' | 'prim' | 'javascript';

safety: 'unsafe' | 'safe' | 'interruptible';

fspec: STRING var '::' sigtype | var '::' sigtype;
// if the entity string is missing, it defaults to the empty string; the meaning of an empty entity
// string depends on the calling convention

//---------------------------------------------------------------------------
// Type signatures

opt_sig: | '::' ctype;

opt_tyconsig: | '::' gtycon;

// Like ktype, but for types that obey the forall-or-nothing rule. See Note [forall-or-nothing rule]
// in GHC.Hs.Type.
sigktype: sigtype | ctype '::' kind;

// Like ctype, but for types that obey the forall-or-nothing rule. See Note [forall-or-nothing rule]
// in GHC.Hs.Type. To avoid duplicating the logic in ctype here, we simply reuse the ctype
// production and perform surgery on the LHsType it returns to turn it into an LHsSigType.
sigtype: ctype;

sig_vars: //- Returned in reversed order
	sig_vars ',' var
	| var;

sigtypes1: sigtype | sigtype ',' sigtypes1;
//---------------------------------------------------------------------------
// Types

unpackedness: '{-# UNPACK' '#-}' | '{-# NOUNPACK' '#-}';

forall_telescope:
	'forall' tv_bndrs '.'
	| 'forall' tv_bndrs '->';

// A ktype is a ctype, possibly with a kind annotation
ktype: ctype | ctype '::' kind;

// A ctype is a for-all type
ctype:
	forall_telescope ctype
	| context '=>' ctype
	| ipvar '::' ctype
	| type;

//--------------------
// Notes for 'context' We parse a context as a btype so that we don't get reduce/reduce errors in
// ctype. The basic problem is that (Eq a, Ord a) looks so much like a tuple type. We can't tell
// until we find the =>

context: btype;

/* Note [GADT decl discards annotations]
 ~~~~~~~~~~~~~~~~~~~~~
 The type production for
 btype
 `->`
 ctype
 add the AnnRarrow annotation twice, in different places.
 This is because if the type
 is
 processed as usual, it belongs on the annotations
 for the type as a whole.
 But if the type
 is
 passed to mkGadtDecl, it discards the top level SrcSpan, and
 the top-level annotation will be
 disconnected. Hence for this specific case it
 is connected to the first type too.
 */

type: // See Note [%shift: type -> btype]
	btype /*shift*/
	| btype '->' ctype
	| btype mult '->' ctype
	| btype '->.' ctype;
// [mu AnnLollyU $2] }

mult: PREFIX_PERCENT atype;

btype: infixtype;

infixtype: // See Note [%shift: infixtype -> ftype]
	ftype /*%shift*/
	| ftype tyop infixtype
	| unpackedness infixtype;

ftype: atype | tyop | ftype tyarg | ftype PREFIX_AT atype;

tyarg: atype | unpackedness atype;

tyop:
	qtyconop
	| tyvarop
	| SIMPLEQUOTE qconop
	| SIMPLEQUOTE varop;

atype:
	ntgtycon //- Not including unit tuples
	// See Note [%shift: atype -> tyvar]
	| tyvar /*%shift*/ //- (See Note [Unit tuples])
	| '*'

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	| PREFIX_TILDE atype
	| PREFIX_BANG atype
	| '{' fielddecls '}'
	// Constructor sigs only
	| '(' ')'
	| '(' ktype ',' comma_types1 ')'
	| '(#' '#)'
	| '(#' comma_types1 '#)'
	| '(#' bar_types2 '#)'
	| '[' ktype ']'
	| '(' ktype ')'
	| quasiquote
	| splice_untyped
	// see Note [Promotion] for the followings
	| SIMPLEQUOTE qcon_nowiredlist
	| SIMPLEQUOTE '(' ktype ',' comma_types1 ')'
	| SIMPLEQUOTE '[' comma_types0 ']'
	| SIMPLEQUOTE var

	// Two or more [ty, ty, ty] must be a promoted list type, just as if you had written '[ty, ty,
	// ty] (One means a list type, zero means the list type constructor, so you have to quote
	// those.)
	| '[' ktype ',' comma_types1 ']'
	| INTEGER
	| CHAR
	| STRING
	| '_';

// An inst_type is what occurs in the head of an instance decl e.g. (Foo a, Gaz b) => Wibble a b
// It's kept as a single type for convenience.
inst_type: sigtype;

deriv_types: sigktype | sigktype ',' deriv_types;

comma_types0: //- Zero or more:  ty,ty,ty
	comma_types1
	| {- empty -};

comma_types1: //- One or more:  ty,ty,ty
	ktype
	| ktype ',' comma_types1;

bar_types2: //- Two or more:  ty|ty|ty
	ktype '|' ktype
	| ktype '|' bar_types2;

tv_bndrs: tv_bndr tv_bndrs | {- empty -};

tv_bndr:
	tv_bndr_no_braces
	| '{' tyvar '}'
	| '{' tyvar '::' kind '}';

tv_bndr_no_braces: tyvar | '(' tyvar '::' kind ')';

fds: {- empty -} | '|' fds1;

fds1: fds1 ',' fd | fd;

fd: varids0 '->' varids0;

varids0: {- empty -} | varids0 tyvar;

//---------------------------------------------------------------------------
// Kinds

kind: ctype;

/* Note [Promotion]
 ~~~~~~~~~~~~~~~~
 - Syntax of promoted qualified names
 We write 'Nat.Zero
 instead of Nat.'Zero when dealing with qualified
 names. Moreover ticks are only allowed in types,
 not in kinds, for a
 few reasons:
 1. we don't need quotes since we cannot define names in kinds
 2. if one day we merge types and kinds, tick would mean look in DataName
 3. we don't have a kind
 namespace anyway
 - Name resolution
 When the user write Zero instead of 'Zero in types, we parse
 it a
 HsTyVar ("Zero", TcClsName) instead of HsTyVar ("Zero", DataName). We
 deal with this in the
 renamer. If a HsTyVar ("Zero", TcClsName) is not
 bounded in the type level, then we look for it
 in
 the term level (we
 change its namespace to DataName, see Note [Demotion] in
 GHC.Types.Names.OccName).
 And both become a HsTyVar ("Zero", DataName) after the renamer.
 */

//---------------------------------------------------------------------------
// Datatype declarations

gadt_constrlist: // Returned in order
	'where' '{' gadt_constrs '}'
	| 'where' vocurly gadt_constrs close
	| {- empty -};

gadt_constrs: gadt_constr ';' gadt_constrs | gadt_constr |;

// We allow the following forms: C :: Eq a => a -> T a C :: forall a. Eq a => !a -> T a D { x,y :: a
// } :: T a forall a. Eq a => D { x,y :: a } :: T a

gadt_constr: optSemi con_list '::' sigtype;
// see Note [Difference in parsing GADT and data constructors] Returns a list because of: C,D :: ty
// TODO:AZ capture the optSemi. Why leading?: optSemi con_list '::' sigtype;

/* Note [Difference in parsing GADT and data constructors]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 GADT constructors have simpler syntax than usual data constructors:
 in GADTs, types cannot occur
 to the left of '::', so they cannot be mixed
 with constructor names (see Note [Parsing data
 constructors is hard]).
 Due to simplified syntax, GADT constructor names (left-hand side of '::')
 use simpler grammar production than usual data constructor names. As a
 consequence, GADT
 constructor names are restricted (names like '(*)' are
 allowed in usual data constructors, but
 not
 in GADTs).
 */
constrs: '=' constrs1;

constrs1: constrs1 '|' constr | constr;

constr: forall context '=>' constr_stuff | forall constr_stuff;

forall: 'forall' tv_bndrs '.' |;

constr_stuff: infixtype;

fielddecls: | fielddecls1;

fielddecls1: fielddecl ',' fielddecls1 | fielddecl;

fielddecl: sig_vars '::' ctype; // A list because of   f,g :: Int

// Reversed!
maybe_derivings: | derivings;

// A list of one or more deriving clauses at the end of a datatype
derivings:
	derivings deriving // AZ: order?
	| deriving;

// The outer Located is just to allow the caller to know the rightmost extremity of the 'deriving'
// clause
deriving:
	'deriving' deriv_clause_types
	| 'deriving' deriv_strategy_no_via deriv_clause_types
	| 'deriving' deriv_clause_types deriv_strategy_via;

deriv_clause_types: qtycon | '(' ')' | '(' deriv_types ')';

//---------------------------------------------------------------------------
// Value definitions

/* Note [Declaration/signature overlap]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 There's an
 awkward
 overlap with a type signature. Consider
 f :: Int -> Int = ...rhs...
 Then we can't tell
 whether
 it's a type signature or a value
 definition with a result signature until we see the
 '='.
 So we
 have to inline enough to postpone reductions until we know.
 */

/* 
 ATTENTION: Dirty Hackery Ahead! If the second alternative of vars is var
 instead of qvar, we
 get another shift/reduce-conflict. Consider the
 following programs:
 { (^^) :: Int->Int ; } Type
 signature; only var allowed
 { (^^) :: Int->Int = ... ; } Value defn with result signature;
 qvar
 allowed (because of instance decls)
 We can't tell whether to reduce var to qvar until after we've
 read the signatures.
 */

decl_no_th:
	sigdecl
	| infixexp opt_sig rhs
	| pattern_synonym_decl;

decl:
	decl_no_th

	// Why do we only allow naked declaration splices in top-level declarations and not here? Short
	// answer: because readFail009 fails terribly with a panic in cvBindsAndSigs otherwise.
	| splice_exp;

rhs: '=' exp wherebinds | gdrhs wherebinds;

gdrhs: gdrhs gdrh | gdrh;

gdrh: '|' guardquals '=' exp;

sigdecl:
	// See Note [Declaration/signature overlap] for why we need infixexp here
	infixexp '::' sigtype
	| var ',' sig_vars '::' sigtype
	| infix prec ops
	| pattern_synonym_sig
	| '{-# COMPLETE' con_list opt_tyconsig '#-}'

	// This rule is for both INLINE and INLINABLE pragmas
	| '{-# INLINE' activation qvarcon '#-}'
	| '{-# SCC' qvar '#-}'
	| '{-# SCC' qvar STRING '#-}'
	| '{-# SPECIALISE' activation qvar '::' sigtypes1 '#-}'
	| '{-# SPECIALISE_INLINE' activation qvar '::' sigtypes1 '#-}'
	| '{-# SPECIALISE' 'instance' inst_type '#-}'

	// A minimal complete definition
	| '{-# MINIMAL' name_boolformula_opt '#-}';

activation: // See Note [%shift: activation -> {- empty -}]
	{- empty -} /*%shift*/
	| explicit_activation;

explicit_activation: //- In brackets
	'[' INTEGER ']'
	| '[' rule_activation_marker INTEGER ']';

//---------------------------------------------------------------------------
// Expressions

quasiquote: TH_QUASIQUOTE | TH_QQUASIQUOTE;

exp:
	infixexp '::' ctype
	| infixexp '-<' exp
	| infixexp '>-' exp
	| infixexp '-<<' exp
	| infixexp '>>-' exp
	// See Note [%shift: exp -> infixexp]
	| infixexp /*shift*/
	| exp_prag_exp; //- See Note [Pragmas and operator fixity]

infixexp:
	exp10
	| infixexp qop exp10p; //- See Note [Pragmas and operator fixity]
// AnnVal annotation for NPlusKPat, which discards the operator

exp10p:
	exp10
	| exp_prag_exp10p; //- See Note [Pragmas and operator fixity]

exp_prag_exp10p: prag_e exp10p;

exp_prag_exp: prag_e exp;

// exp_prag(e) : prag_e e //- See Note [Pragmas and operator fixity] {% runPV (unECP $2) >>= \ $2 ->
// fmap ecpFromExp $ return $ (reLocA $ sLLlA $1 $> $ HsPragE noExtField (unLoc $1) $2) };

exp10: // See Note [%shift: exp10 -> '-' fexp]
	'-' fexp /*%shift*/
	// See Note [%shift: exp10 -> fexp]
	| fexp /*%shift*/;

optSemi: ';' |;

/* Note [Pragmas and operator fixity]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 'prag_e' is an
 expression pragma, such as {-# SCC ... #-}.
 It must be used with care, or else #15730 happens.
 Consider this infix
 expression:
 1 / 2 / 2
 There are two ways to parse it:
 1. (1 / 2) / 2 =
 0.25
 2. 1 / (2 / 2) = 1.0
 Due to the fixity of the (/) operator (assuming it comes from
 Prelude),
 option 1 is the correct parse. However, in the past GHC's parser used to get
 confused
 by the SCC annotation when it occurred in the middle of an infix
 expression:
 1 / {-# SCC ann #-}
 2 / 2 -- used to get parsed as option 2
 There are several ways to address this issue, see GHC
 Proposal #176 for a
 detailed exposition:
 https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0176-scc-parsing.rst
 The
 accepted fix is to disallow pragmas that occur within infix expressions.
 Infix expressions are
 assembled out of 'exp10', so 'exp10' must not accept
 pragmas. Instead, we accept them in exactly
 two places:
 at the start of an expression or a parenthesized subexpression:
 f = {-# SCC ann #-}
 1
 / 2 / 2 -- at the start of the expression
 g = 5 + ({-# SCC ann #-} 1 / 2 / 2) -- at the start
 of a
 parenthesized subexpression
 immediately after the last operator:
 f = 1 / 2 / {-# SCC ann
 #-} 2
 In both cases, the parse does not depend on operator fixity. The second case
 may sound
 unnecessary, but it's actually needed to support a common idiom:
 f $ {-# SCC ann $-} ...
 */
prag_e: '{-# SCC' STRING '#-}' | '{-# SCC' VARID '#-}';

fexp:
	fexp aexp

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	| fexp PREFIX_AT atype
	| 'static' aexp
	| aexp;

aexp: // See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	qvar TIGHT_INFIX_AT aexp

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	| PREFIX_TILDE aexp
	| PREFIX_BANG aexp
	| PREFIX_MINUS aexp
	| '\\' apats '->' exp
	| 'let' binds 'in' exp
	| '\\' 'lcase' altslist
	| 'if' exp optSemi 'then' exp optSemi 'else' exp
	| 'if' ifgdpats
	| 'case' exp 'of' altslist
	// QualifiedDo.
	| DO stmtlist
	| MDO stmtlist
	| 'proc' aexp '->' exp
	| aexp1;

aexp1:
	aexp1 '{' fbinds '}'

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	| aexp1 TIGHT_INFIX_PROJ field
	| aexp2;

aexp2:
	qvar
	| qcon
	// See Note [%shift: aexp2 -> ipvar]
	| ipvar /*shift */
	| overloaded_label
	| literal
	// This will enable overloaded strings permanently. Normally the renamer turns HsString into
	// HsOverLit when -XOverloadedStrings is on. | STRING { sL (getLoc $1) (HsOverLit $!
	// mkHsIsString (getSTRINGs $1) (getSTRING $1) noExtField) }
	| INTEGER
	| RATIONAL

	// N.B.: sections get parsed by these next two productions. This allows you to write, e.g., '(+
	// 3, 4 -)', which isn't correct Haskell (you'd have to write '((+ 3), (4 -))') but the less
	// cluttered version fell out of having texps.
	| '(' texp ')'
	| '(' tup_exprs ')'

	// This case is only possible when 'OverloadedRecordDotBit' is enabled.
	| '(' projection ')'
	| '(#' texp '#)'
	| '(#' tup_exprs '#)'
	| '[' list ']'
	| '_'

	// Template Haskell Extension
	| splice_untyped
	| splice_typed
	| SIMPLEQUOTE qvar
	| SIMPLEQUOTE qcon
	| TH_TY_QUOTE tyvar
	| TH_TY_QUOTE gtycon
	// See Note [%shift: aexp2 -> TH_TY_QUOTE]
	| TH_TY_QUOTE /*shift */
	| '[|' exp '|]'
	| '[||' exp '||]'
	| '[t|' ktype '|]'
	| '[p|' infixexp '|]'
	| '[d|' cvtopbody '|]'
	| quasiquote

	// arrow notation extension
	| '(|' aexp cmdargs '|)';

projection: // See Note [Whitespace-sensitive operator parsing] in GHC.Parsing.Lexer
	projection TIGHT_INFIX_PROJ field
	| PREFIX_PROJ field;

splice_exp: splice_untyped | splice_typed;

splice_untyped: // See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	PREFIX_DOLLAR aexp2;

splice_typed: // See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer
	PREFIX_DOLLAR_DOLLAR aexp2;

cmdargs: cmdargs acmd |;

acmd: aexp;

cvtopbody: '{' cvtopdecls0 '}' | vocurly cvtopdecls0 close;

cvtopdecls0: topdecls_semi | topdecls;

//---------------------------------------------------------------------------
// Tuple expressions

// "texp" is short for tuple expressions: things that can appear unparenthesized as long as they're
// inside parens or delimited by commas
texp:
	exp

	// Note [Parsing sections] ~~~~~~~~~~~~~~~~~~~~~~~ We include left and right sections here,
	// which isn't technically right according to the Haskell standard. For example (3 +, True)
	// isn't legal. However, we want to parse bang patterns like (!x, !y) and it's convenient to do
	// so here as a section Then when converting expr to pattern we unravel it again Meanwhile, the
	// renamer checks that real sections appear inside parens.
	| infixexp qop
	| qopm infixexp

	// View patterns get parenthesized above
	| exp '->' texp;

// Always at least one comma or bar. Though this can parse just commas (without any expressions), it
// won't in practice, because (,,,) is parsed as a name. See Note [ExplicitTuple] in GHC.Hs.Expr.
tup_exprs:
	texp commas_tup_tail
	| commas tup_tail
	| texp bars
	| bars texp bars0;

// Always starts with commas; always follows an expr
commas_tup_tail: commas tup_tail;

// Always follows a comma
tup_tail:
	texp commas_tup_tail
	| texp
	// See Note [%shift: tup_tail -> {- empty -}]
	| /*%shift*/;

//---------------------------------------------------------------------------
// List expressions

// The rules below are little bit contorted to keep lexps left-recursive while avoiding another
// shift/reduce-conflict. Never empty.
list:
	texp
	| lexps
	| texp '..'
	| texp ',' exp '..'
	| texp '..' exp
	| texp ',' exp '..' exp
	| texp '|' flattenedpquals;

lexps: lexps ',' texp | texp ',' texp;

//---------------------------------------------------------------------------
// List Comprehensions

flattenedpquals: pquals;

pquals: squals '|' pquals | squals;

squals: // one can "grab" the earlier ones
	squals ',' transformqual
	| squals ',' qual
	| transformqual
	| qual;
// | transformquals1 ',' '{|' pquals '|}' { sLL $1 $> ($4 : unLoc $1) } | '{|' pquals '|}' { sL1 $1
// [$2] }

// It is possible to enable bracketing (associating) qualifier lists by uncommenting the lines with
// {| |} above. Due to a lack of consensus on the syntax, this feature is not being used until we
// get user demand.

transformqual: // Function is applied to a list of stmts *in order*
	'then' exp
	| 'then' exp 'by' exp
	| 'then' 'group' 'using' exp
	| 'then' 'group' 'by' exp 'using' exp;

// Note that 'group' is a special_id, which means that you can enable TransformListComp while still
// using Data.List.group. However, this introduces a shift/reduce conflict. Happy chooses to resolve
// the conflict in by choosing the "group by" variant, which is what we want.

//---------------------------------------------------------------------------
// Guards

guardquals: guardquals1;

guardquals1: guardquals1 ',' qual | qual;

//---------------------------------------------------------------------------
// Case alternatives

altslist:
	'{' alts '}'
	| vocurly alts close
	| '{' '}'
	| vocurly close;

alts: alts1 | ';' alts;

alts1: alts1 ';' alt | alts1 ';' | alt;

alt: pat alt_rhs;

alt_rhs: ralt wherebinds;

ralt: '->' exp | gdpats;

gdpats: gdpats gdpat | gdpat;

// layout for MultiWayIf doesn't begin with an open brace, because it's hard to generate the open
// brace in addition to the vertical bar in the lexer, and we don't need it.
ifgdpats: '{' gdpats '}' | gdpats close;

gdpat: '|' guardquals '->' exp;

// 'pat' recognises a pattern, including one with a bang at the top e.g. "!x" or "!(x,y)" or "C a b"
// etc Bangs inside are parsed as infix operator applications, so that we parse them right when
// bang-patterns are off
pat: exp;

bindpat: exp;

apat: aexp;

apats: apat apats | {- empty -};

//---------------------------------------------------------------------------
// Statement sequences

stmtlist: '{' stmts '}' | vocurly stmts close;

// do { ;; s ; s ; ; s ;; } The last Stmt should be an expression, but that's hard to enforce here,
// because we need too much lookahead if we see do { e ; } So we use BodyStmts throughout, and
// switch the last one over in ParseUtils.checkDo instead

stmts: stmts ';' stmt | stmts ';' | stmt |;

// For typing stmts at the GHCi prompt, where the input may consist of just comments.
maybe_stmt: stmt |;

// For GHC API.
e_stmt: stmt;

stmt: qual | 'rec' stmtlist;

qual: bindpat '<-' exp | exp | 'let' binds;

//---------------------------------------------------------------------------
// Record Field Update/Construction

fbinds: fbinds1 | {- empty -};

fbinds1: fbind ',' fbinds1 | fbind | '..';

fbind:
	qvar '=' texp
	// RHS is a 'texp', allowing view patterns (#6038) and, incidentally, sections. Eg f (R { x =
	// show -> s }) = ...
	| qvar
	// In the punning case, use a place-holder The renamer fills in the final value

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer AZ: need to pull out the
	// let block into a helper
	| field TIGHT_INFIX_PROJ fieldToUpdate '=' texp

	// See Note [Whitespace-sensitive operator parsing] in GHC.Parser.Lexer AZ: need to pull out the
	// let block into a helper
	| field TIGHT_INFIX_PROJ fieldToUpdate;

fieldToUpdate: // See Note [Whitespace-sensitive operator parsing] in Lexer.x
	fieldToUpdate TIGHT_INFIX_PROJ field
	| field;

//---------------------------------------------------------------------------
// Implicit Parameter Bindings

dbinds: dbinds ';' dbind | dbinds ';'; //- reversed
//      | {- empty -}                  { [] }

dbind: ipvar '=' exp;

ipvar: IPDUPVARID;

//---------------------------------------------------------------------------
// Overloaded labels

overloaded_label: LABELVARID;

//---------------------------------------------------------------------------
// Warnings and deprecations

name_boolformula_opt: name_boolformula | {- empty -};

name_boolformula:
	name_boolformula_and
	| name_boolformula_and '|' name_boolformula;

name_boolformula_and: name_boolformula_and_list;

name_boolformula_and_list:
	name_boolformula_atom
	| name_boolformula_atom ',' name_boolformula_and_list;

name_boolformula_atom: '(' name_boolformula ')' | name_var;

namelist: name_var | name_var ',' namelist;

name_var: var | con;

//---------------------------------------
// Data constructors There are two different productions here as lifted list constructors are parsed
// differently.

qcon_nowiredlist: gen_qcon | sysdcon_nolist;

qcon: gen_qcon | sysdcon;

gen_qcon: qconid | '(' qconsym ')';

con: conid | '(' consym ')' | sysdcon;

con_list: con | con ',' con_list;

// See Note [ExplicitTuple] in GHC.Hs.Expr
sysdcon_nolist: //- Wired in data constructors
	'(' ')'
	| '(' commas ')'
	| '(#' '#)'
	| '(#' commas '#)';

// See Note [Empty lists] in GHC.Hs.Expr
sysdcon: sysdcon_nolist | '[' ']';

conop: consym | '`' conid '`';

qconop: qconsym | '`' qconid '`';

//--------------------------------------------------------------------------
// Type constructors

// See Note [Unit tuples] in GHC.Hs.Type for the distinction between gtycon and ntgtycon
gtycon: //- A "general" qualified tycon, including unit tuples
	ntgtycon
	| '(' ')'
	| '(#' '#)';

ntgtycon: //- A "general" qualified tycon, excluding unit tuples
	oqtycon
	| '(' commas ')'
	| '(#' commas '#)'
	| '(#' bars '#)'
	| '(' '->' ')'
	| '[' ']';

oqtycon: //- An "ordinary" qualified tycon;
	qtycon
	| '(' qtyconsym ')'; // These can appear in export lists

oqtycon_no_varcon: //- Type constructor which cannot be mistaken
	qtycon
	| '(' QCONSYM ')'
	| '(' CONSYM ')'
	| '(' ':' ')';
// for variable constructor in export lists see Note [Type constructors in export list]: qtycon | '(' QCONSYM ')' | '(' CONSYM ')' | '(' ':' ')';

/* Note [Type constructors in export list]
 ~~~~~~~~~~~~~~~~~~~~~
 Mixing type constructors and
 data
 constructors in export lists introduces
 ambiguity in grammar: e.g. (*) may be both a type
 constructor and a function.
 -XExplicitNamespaces allows to disambiguate by explicitly prefixing
 type
 constructors with 'type' keyword.
 This ambiguity causes reduce/reduce conflicts in parser,
 which are always
 resolved in favour of data constructors. To get rid of conflicts we demand
 that
 ambiguous type constructors (those, which are formed by the same
 productions as variable
 constructors) are always prefixed with 'type' keyword.
 Unambiguous type constructors may occur
 both with or without 'type' keyword.
 Note that in the parser we still parse data constructors as
 type
 constructors. As such, they still end up in the type constructor namespace
 until after
 renaming when we resolve the proper namespace for each exported
 child.
 */
qtyconop: // See Note [%shift: qtyconop -> qtyconsym]
	qtyconsym /*shift  */
	| '`' qtycon '`';

qtycon: QCONID | tycon; //- Qualified or unqualified

tycon: CONID; //- Unqualified

qtyconsym: QCONSYM | QVARSYM | tyconsym;

tyconsym: CONSYM | VARSYM | ':' | '-' | '.';

// An "ordinary" unqualified tycon. See `oqtycon` for the qualified version. These can appear in
// `ANN type` declarations (#19374).
otycon: tycon | '(' tyconsym ')';

//---------------------------------------------------------------------------
// Operators

op: varop | conop | '->'; //- used in infix decls

varop: varsym | '`' varid '`';

qop: qvarop | qconop | hole_op; //- used in sections

qopm: qvaropm | qconop | hole_op; //- used in sections

// used in sections
hole_op: '`' '_' '`';

qvarop: qvarsym | '`' qvarid '`';

qvaropm: qvarsym_no_minus | '`' qvarid '`';

//---------------------------------------------------------------------------
// Type variables

tyvar: tyvarid;

tyvarop: '`' tyvarid '`';

tyvarid:
	VARID
	| special_id
	| 'unsafe'
	| 'safe'
	| 'interruptible';
// If this changes relative to varid, update 'checkRuleTyVarBndrNames' in GHC.Parser.PostProcess See
// Note [Parsing explicit foralls in Rules]

//---------------------------------------------------------------------------
// Variables

var: varid | '(' varsym ')';

qvar: qvarid | '(' varsym ')' | '(' qvarsym1 ')';
// We've inlined qvarsym here so that the decision about whether it's a qvar or a var can be
// postponed until *after* we see the close paren.

field: varid;

qvarid: varid | QVARID;

// Note that 'role' and 'family' get lexed separately regardless of the use of extensions. However,
// because they are listed here, this is OK and they can be used as normal varids. See Note [Lexing
// type pseudo-keywords] in GHC.Parser.Lexer
varid:
	VARID
	| special_id
	| 'unsafe'
	| 'safe'
	| 'interruptible'
	| 'forall'
	| 'family'
	| 'role';
// If this changes relative to tyvarid, update 'checkRuleTyVarBndrNames' in GHC.Parser.PostProcess
// See Note [Parsing explicit foralls in Rules]

qvarsym: varsym | qvarsym1;

qvarsym_no_minus: varsym_no_minus | qvarsym1;

qvarsym1: QVARSYM;

varsym: varsym_no_minus | '-';

varsym_no_minus: //- varsym not including '-'
	VARSYM
	| special_sym;

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
	// See Note [%shift: special_id -> 'group']
	| 'group' /*shift */
	| 'stock'
	| 'anyclass'
	| 'via'
	| 'unit'
	| 'dependency'
	| 'signature';

special_sym: '.' | '*';

//---------------------------------------------------------------------------
// Data constructors

qconid: conid | QCONID; //- Qualified or unqualified

conid: CONID;

qconsym: consym | QCONSYM; //- Qualified or unqualified

consym:
	CONSYM

	// ':' means only list cons
	| ':';

//---------------------------------------------------------------------------
// Literals

literal:
	CHAR
	| STRING
	| PRIMINTEGER
	| PRIMWORD
	| PRIMCHAR
	| PRIMSTRING
	| PRIMFLOAT
	| PRIMDOUBLE;

//---------------------------------------------------------------------------
// Layout

close:
	vccurly //- context popped in lexer.
	| /*error*/;

//---------------------------------------------------------------------------
// Miscellaneous (mostly renamings)

modid: CONID | QCONID;

commas: commas ',' | ','; //- One or more commas

bars0: bars |; //- Zero or more bars

bars: bars '|' | '|'; //- One or more bars
