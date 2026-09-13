theory FREnv_BetaSigma_Congruence
  imports FREnv_BetaSigma
begin

text \<open>
  Congruence closure of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>\<^sup>*"} on @{text "lambda_FREnv"}: each of
  the six congruence rules lifts from a single step to a whole chain.
  The counterpart of @{text "EnvEps.EnvEps_Sigma_Congruence"} for this
  calculus, needed by the translation simulation lemma
  (@{text "EnvEps.EnvEps_FREnv_Translation_Simulation"}, roadmap 29),
  whose congruence cases have to transport an induction hypothesis
  through a surrounding constructor.
\<close>

lemma bs_steps_AppL [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma>\<^sup>* App M' N"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.AppL rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_AppR [intro]: "N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma>\<^sup>* App M N'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.AppR rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_Lam [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> Lam x M \<rightarrow>\<beta>\<sigma>\<^sup>* Lam x M'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.Lam rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_ExtnL [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M' x N"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.ExtnL rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_ExtnR [intro]: "N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M x N'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.ExtnR rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_EnvAbst [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> Eps M \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.EnvAbst rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_App [intro]:
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma>\<^sup>* App M' N'"
  using bs_steps_AppL bs_steps_AppR by (blast intro: rtranclp_trans)

lemma bs_steps_Ext [intro]:
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M' x N'"
  using bs_steps_ExtnL bs_steps_ExtnR by (blast intro: rtranclp_trans)

lemma bs_step_into_steps [intro]: "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> M \<rightarrow>\<beta>\<sigma>\<^sup>* N"
  by (rule r_into_rtranclp)

end
