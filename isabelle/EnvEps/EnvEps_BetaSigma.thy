theory EnvEps_BetaSigma
  imports EnvEps_Sigma
begin

text \<open>
  The one-step reduction relation @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} on @{text "lambda_EnvEps"}
  terms (docs file @{text "docs/enve-reduction-beta-sigma.md"}). This
  extends @{text "\<rightarrow>\<sigma>"} (@{text "EnvEps_Sigma.sigma_step"}) with three
  beta rules: @{text Beta}, @{text BetaClos}, and @{text "Comp\<^sub>\<epsilon>"} (the
  rule turning @{term "App (Eps M) N"} into @{term "Comp M N"}).
\<close>

inductive beta_sigma_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<sigma>" 50) where
  Beta:
    "App (Lam x M) N \<rightarrow>\<beta>\<sigma> Comp M (Ext N x Id)"
| BetaClos:
    "App (Comp (Lam x M) L) N \<rightarrow>\<beta>\<sigma> Comp M (Ext N x L)"
| CompEps:
    "App (Eps M) N \<rightarrow>\<beta>\<sigma> Comp M N"
| Assoc:
    "Comp (Comp M N) L \<rightarrow>\<beta>\<sigma> Comp M (Comp N L)"
| IdL:
    "Comp Id M \<rightarrow>\<beta>\<sigma> M"
| IdR:
    "Comp M Id \<rightarrow>\<beta>\<sigma> M"
| DExtn:
    "Comp (Ext L x M) N \<rightarrow>\<beta>\<sigma> Ext (Comp L N) x (Comp M N)"
| VarRef:
    "Comp (Var x) (Ext M x N) \<rightarrow>\<beta>\<sigma> M"
| VarSkip:
    "x \<noteq> y \<Longrightarrow> Comp (Var x) (Ext M y N) \<rightarrow>\<beta>\<sigma> Comp (Var x) N"
| DApp:
    "Comp (App M N) L \<rightarrow>\<beta>\<sigma> App (Comp M L) (Comp N L)"
| EpsEps:
    "Comp (Eps M) N \<rightarrow>\<beta>\<sigma> Eps M"
| AppL:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma> App M' N"
| AppR:
    "N \<rightarrow>\<beta>\<sigma> N' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma> App M N'"
| Lam:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Lam x M \<rightarrow>\<beta>\<sigma> Lam x M'"
| ExtnL:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma> Ext M' x N"
| ExtnR:
    "N \<rightarrow>\<beta>\<sigma> N' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma> Ext M x N'"
| CompL:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Comp M N \<rightarrow>\<beta>\<sigma> Comp M' N"
| CompR:
    "N \<rightarrow>\<beta>\<sigma> N' \<Longrightarrow> Comp M N \<rightarrow>\<beta>\<sigma> Comp M N'"
| Eop:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Eps M \<rightarrow>\<beta>\<sigma> Eps M'"

text \<open>
  The reflexive-transitive closure @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>\<^sup>*"}.
\<close>

abbreviation beta_sigma_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<sigma>\<^sup>*" 50) where
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* N \<equiv> beta_sigma_step\<^sup>*\<^sup>* M N"

text \<open>
  Sanity check: every @{text "\<rightarrow>\<sigma>"} step is also a @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} step.
\<close>

lemma sigma_step_is_beta_sigma_step:
  assumes "M \<rightarrow>\<sigma> N"
  shows "M \<rightarrow>\<beta>\<sigma> N"
  using assms
  by (induction rule: sigma_step.induct)
     (blast intro: beta_sigma_step.intros)+

end
