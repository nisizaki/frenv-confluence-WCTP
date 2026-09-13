theory FREnv_Syntax
  imports Main
begin

text \<open>
  Syntax of @{text "lambda_FREnv"}, the untyped lambda calculus with
  functionally referable environments (docs file
  @{text "docs/frenv-syntax.md"}).

  As in @{text "lambda_EnvEps"} (see @{text "EnvEps/EnvEps_Syntax.thy"}),
  @{term Lam} is \<^emph>\<open>not\<close> a binder at the syntax level: the name argument
  of @{term Lam} and of @{term Ext} is plain first-order data, not a
  meta-level binder. Consequently no alpha-equivalence quotient, nominal
  binder type, or de Bruijn representation is used here; name resolution
  is handled entirely by the reduction relation (to be defined in later
  theories), not by the term datatype.

  There are no constants in either calculus, so there is no @{text Const}
  constructor.

  This @{text trm} datatype has six constructors, one fewer than
  @{text "EnvEps.trm"}: @{text "lambda_FREnv"} has no @{text Comp}
  constructor, since environment composition is not a syntactic primitive
  here (unlike in @{text "lambda_EnvEps"}).
\<close>

type_synonym name = string

datatype trm =
    Var  name
  | Lam  name trm
  | App  trm trm
  | Id
  | Ext  trm name trm
  | Eps  trm

end
