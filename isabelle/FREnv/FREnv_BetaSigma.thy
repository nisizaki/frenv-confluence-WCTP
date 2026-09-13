theory FREnv_BetaSigma
  imports FREnv_Sigma
begin

text \<open>
  The one-step reduction relation @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} on @{text "lambda_FREnv"}
  terms (docs file @{text "docs/frenv-reduction-beta-sigma.md"}). This
  extends @{text "\<rightarrow>\<sigma>"} (@{text "FREnv_Sigma.sigma_step"}) with the two
  beta rules @{text Beta} and @{text BetaClos}; all non-beta computation
  rules and all compatibility rules are the same as for @{text "\<rightarrow>\<sigma>"},
  restated here so that @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} is defined as its own least
  relation (matching how the thesis presents it), rather than as a mere
  union with @{text "\<rightarrow>\<sigma>"}.
\<close>

inductive beta_sigma_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<sigma>" 50) where
  Beta:
    "App (Lam x M) N \<rightarrow>\<beta>\<sigma> App (Eps M) (Ext N x Id)"
| BetaClos:
    "App (App (Eps (Lam x M)) L) N \<rightarrow>\<beta>\<sigma> App (Eps M) (Ext N x L)"
| Assoc:
    "App (Eps (App (Eps L) M)) N \<rightarrow>\<beta>\<sigma> App (Eps L) (App (Eps M) N)"
| IdL:
    "App (Eps Id) M \<rightarrow>\<beta>\<sigma> M"
| IdR:
    "App (Eps M) Id \<rightarrow>\<beta>\<sigma> M"
| DExtn:
    "App (Eps (Ext L x M)) N \<rightarrow>\<beta>\<sigma> Ext (App (Eps L) N) x (App (Eps M) N)"
| VarRef:
    "App (Eps (Var x)) (Ext M x N) \<rightarrow>\<beta>\<sigma> M"
| VarSkip:
    "x \<noteq> y \<Longrightarrow> App (Eps (Var y)) (Ext M x N) \<rightarrow>\<beta>\<sigma> App (Eps (Var y)) N"
| DApp:
    "App (Eps (App M N)) L \<rightarrow>\<beta>\<sigma> App (App (Eps M) L) (App (Eps N) L)"
| EpsEps:
    "App (Eps (Eps M)) N \<rightarrow>\<beta>\<sigma> Eps M"
| AppL:
    "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> App M L \<rightarrow>\<beta>\<sigma> App N L"
| AppR:
    "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> App L M \<rightarrow>\<beta>\<sigma> App L N"
| Lam:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Lam x M \<rightarrow>\<beta>\<sigma> Lam x M'"
| ExtnL:
    "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> Ext M x L \<rightarrow>\<beta>\<sigma> Ext N x L"
| ExtnR:
    "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> Ext L x M \<rightarrow>\<beta>\<sigma> Ext L x N"
| EnvAbst:
    "M \<rightarrow>\<beta>\<sigma> M' \<Longrightarrow> Eps M \<rightarrow>\<beta>\<sigma> Eps M'"

text \<open>
  The reflexive-transitive closure @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>\<^sup>*"}.
\<close>

abbreviation beta_sigma_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<sigma>\<^sup>*" 50) where
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* N \<equiv> beta_sigma_step\<^sup>*\<^sup>* M N"

text \<open>
  Sanity check: every @{text "\<rightarrow>\<sigma>"} step is also a @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} step,
  i.e. @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} really does extend @{text "\<rightarrow>\<sigma>"} as claimed above.
\<close>

lemma sigma_step_is_beta_sigma_step:
  assumes "M \<rightarrow>\<sigma> N"
  shows "M \<rightarrow>\<beta>\<sigma> N"
  using assms
  by (induction rule: sigma_step.induct)
     (blast intro: beta_sigma_step.intros)+

end
