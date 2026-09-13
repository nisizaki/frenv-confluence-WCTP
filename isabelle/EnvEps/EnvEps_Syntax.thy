theory EnvEps_Syntax
  imports Main
begin

text \<open>
  Syntax of @{text "lambda_EnvEps"}, the untyped lambda calculus with
  environments and environment abstraction (thesis Definition 4, docs
  file @{text "docs/enve-syntax.md"}).

  As in @{text "lambda_FREnv"}, @{term Lam} is \<^emph>\<open>not\<close> a binder at the
  syntax level: the name argument of @{term Lam} and of @{term Ext} is
  plain first-order data, not a meta-level binder. Consequently no
  alpha-equivalence quotient, nominal binder type, or de Bruijn
  representation is used here; name resolution is handled entirely by
  the reduction relation (to be defined in later theories), not by the
  term datatype.

  There are no constants in either calculus, so there is no @{text Const}
  constructor.
\<close>

type_synonym name = string

datatype trm =
    Var  name
  | Id
  | App  trm trm
  | Ext  trm name trm
  | Lam  name trm
  | Comp trm trm
  | Eps  trm

end
