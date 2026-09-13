theory EnvEps_BetaSigma_Congruence
  imports EnvEps_BetaSigma
begin

text \<open>
  Congruence closure of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>\<^sup>*"} on @{text "lambda_EnvEps"}: each of
  the eight congruence rules lifts from a single step to a whole chain.
  The counterpart of @{text "FREnv.FREnv_BetaSigma_Congruence"} for this
  calculus (which needs only six, since @{text "lambda_FREnv"} has no
  @{text Comp} constructor), needed by the translation lifting lemma
  (@{text EnvEps_FREnv_Translation_Lifting}, roadmap 30).
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

lemma bs_steps_Eop [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> Eps M \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.Eop rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_CompL [intro]: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> Comp M N \<rightarrow>\<beta>\<sigma>\<^sup>* Comp M' N"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.CompL rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_CompR [intro]: "N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> Comp M N \<rightarrow>\<beta>\<sigma>\<^sup>* Comp M N'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_sigma_step.CompR rtranclp.rtrancl_into_rtrancl)

lemma bs_steps_App [intro]:
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> App M N \<rightarrow>\<beta>\<sigma>\<^sup>* App M' N'"
  using bs_steps_AppL bs_steps_AppR by (blast intro: rtranclp_trans)

lemma bs_steps_Ext [intro]:
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> Ext M x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M' x N'"
  using bs_steps_ExtnL bs_steps_ExtnR by (blast intro: rtranclp_trans)

lemma bs_steps_Comp [intro]:
  "M \<rightarrow>\<beta>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<beta>\<sigma>\<^sup>* N' \<Longrightarrow> Comp M N \<rightarrow>\<beta>\<sigma>\<^sup>* Comp M' N'"
  using bs_steps_CompL bs_steps_CompR by (blast intro: rtranclp_trans)

lemma bs_step_into_steps [intro]: "M \<rightarrow>\<beta>\<sigma> N \<Longrightarrow> M \<rightarrow>\<beta>\<sigma>\<^sup>* N"
  by (rule r_into_rtranclp)

end
