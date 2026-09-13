theory EnvEps_Sigma
  imports EnvEps_Syntax
begin

text \<open>
  The one-step sub-reduction relation @{text "\<rightarrow>\<^sub>\<sigma>"} on
  @{text "lambda_EnvEps"} terms (docs file
  @{text "docs/enve-reduction-sigma.md"}). Unlike @{text "lambda_FREnv"},
  the substitution rules here act on the primitive @{term Comp}
  constructor rather than directly on @{term "App (Eps M) N"}; the rule
  turning @{term "App (Eps M) N"} into @{term "Comp M N"}
  (@{text "Comp\<^sub>\<epsilon>"}) is a beta rule and is defined later, in
  @{text EnvEps_BetaSigma}, not here.
\<close>

inductive sigma_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<sigma>" 50) where
  Assoc:
    "Comp (Comp M N) L \<rightarrow>\<sigma> Comp M (Comp N L)"
| IdL:
    "Comp Id M \<rightarrow>\<sigma> M"
| IdR:
    "Comp M Id \<rightarrow>\<sigma> M"
| DExtn:
    "Comp (Ext L x M) N \<rightarrow>\<sigma> Ext (Comp L N) x (Comp M N)"
| VarRef:
    "Comp (Var x) (Ext M x N) \<rightarrow>\<sigma> M"
| VarSkip:
    "x \<noteq> y \<Longrightarrow> Comp (Var x) (Ext M y N) \<rightarrow>\<sigma> Comp (Var x) N"
| DApp:
    "Comp (App M N) L \<rightarrow>\<sigma> App (Comp M L) (Comp N L)"
| EpsEps:
    "Comp (Eps M) N \<rightarrow>\<sigma> Eps M"
| AppL:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> App M N \<rightarrow>\<sigma> App M' N"
| AppR:
    "N \<rightarrow>\<sigma> N' \<Longrightarrow> App M N \<rightarrow>\<sigma> App M N'"
| Lam:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Lam x M \<rightarrow>\<sigma> Lam x M'"
| ExtnL:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Ext M x N \<rightarrow>\<sigma> Ext M' x N"
| ExtnR:
    "N \<rightarrow>\<sigma> N' \<Longrightarrow> Ext M x N \<rightarrow>\<sigma> Ext M x N'"
| CompL:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Comp M N \<rightarrow>\<sigma> Comp M' N"
| CompR:
    "N \<rightarrow>\<sigma> N' \<Longrightarrow> Comp M N \<rightarrow>\<sigma> Comp M N'"
| Eop:
    "M \<rightarrow>\<sigma> M' \<Longrightarrow> Eps M \<rightarrow>\<sigma> Eps M'"

text \<open>
  The reflexive-transitive closure @{text "\<rightarrow>\<^sub>\<sigma>\<^sup>*"}.
\<close>

abbreviation sigma_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<sigma>\<^sup>*" 50) where
  "M \<rightarrow>\<sigma>\<^sup>* N \<equiv> sigma_step\<^sup>*\<^sup>* M N"

end
