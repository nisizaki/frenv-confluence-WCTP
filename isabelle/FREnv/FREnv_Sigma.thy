theory FREnv_Sigma
  imports FREnv_Syntax
begin

text \<open>
  The one-step sub-reduction relation @{text "\<rightarrow>\<^sub>\<sigma>"} on
  @{text "lambda_FREnv"} terms (docs file
  @{text "docs/frenv-reduction-sigma.md"}).

  Notation used in the docs file translates to constructors as follows:
  @{text "\<epsilon>(M) N"} is @{term "App (Eps M) N"}; @{text "M N"} is
  @{term "App M N"}; @{text "\<lambda>x. M"} is @{term "Lam x M"};
  @{text "(M/x)\<cdot>N"} is @{term "Ext M x N"}; @{text "id"} is
  @{term Id}; @{text "\<epsilon>(M)"} is @{term "Eps M"}.

  As in the docs file, this relation has no @{text Const} rule: neither
  calculus has a constant-valued term former.
\<close>

inductive sigma_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<sigma>" 50) where
  Assoc:
    "App (Eps (App (Eps L) M)) N \<rightarrow>\<sigma> App (Eps L) (App (Eps M) N)"
| IdL:
    "App (Eps Id) M \<rightarrow>\<sigma> M"
| IdR:
    "App (Eps M) Id \<rightarrow>\<sigma> M"
| DExtn:
    "App (Eps (Ext L x M)) N \<rightarrow>\<sigma> Ext (App (Eps L) N) x (App (Eps M) N)"
| VarRef:
    "App (Eps (Var x)) (Ext M x N) \<rightarrow>\<sigma> M"
| VarSkip:
    "x \<noteq> y \<Longrightarrow> App (Eps (Var y)) (Ext M x N) \<rightarrow>\<sigma> App (Eps (Var y)) N"
| DApp:
    "App (Eps (App M N)) L \<rightarrow>\<sigma> App (App (Eps M) L) (App (Eps N) L)"
| EpsEps:
    "App (Eps (Eps M)) N \<rightarrow>\<sigma> Eps M"
| AppL:
    "M \<rightarrow>\<sigma> N \<Longrightarrow> App M L \<rightarrow>\<sigma> App N L"
| AppR:
    "M \<rightarrow>\<sigma> N \<Longrightarrow> App L M \<rightarrow>\<sigma> App L N"
| Lam:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Lam x M \<rightarrow>\<sigma> Lam x M'"
| ExtnL:
    "M \<rightarrow>\<sigma> N \<Longrightarrow> Ext M x L \<rightarrow>\<sigma> Ext N x L"
| ExtnR:
    "M \<rightarrow>\<sigma> N \<Longrightarrow> Ext L x M \<rightarrow>\<sigma> Ext L x N"
| EnvAbst:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Eps M \<rightarrow>\<sigma> Eps M'"

text \<open>
  The reflexive-transitive closure @{text "\<rightarrow>\<^sub>\<sigma>\<^sup>*"}: @{text "M \<rightarrow>\<sigma>\<^sup>* N"}
  means @{term M} reduces to @{term N} in zero or more @{text "\<rightarrow>\<sigma>"} steps.
\<close>

abbreviation sigma_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<sigma>\<^sup>*" 50) where
  "M \<rightarrow>\<sigma>\<^sup>* N \<equiv> sigma_step\<^sup>*\<^sup>* M N"

end
