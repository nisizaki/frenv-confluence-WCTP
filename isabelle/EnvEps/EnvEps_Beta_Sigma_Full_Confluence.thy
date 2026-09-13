theory EnvEps_Beta_Sigma_Full_Confluence
  imports EnvEps_Beta_Over_Sigma_Confluence EnvEps_Beta_Normal_Form_Simulation
begin

text \<open>
  Confluence of @{text "\<lambda>\<^sub>E\<^sub>n\<^sub>v\<epsilon>"}'s full @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} on all terms
  (docs file @{text "docs/enve-beta-sigma-full-confluence.md"}, thesis
  Theorem 13; roadmap item 26), assembled directly from Theorem 7
  (@{text beta_step_simulated_by_beta_over_sigma}), Theorem 12
  (@{text beta_over_sigma_confluent}), and basic @{text "\<sigma>"}-normal-form
  facts, bypassing the thesis's unrecoverable "Theorem 1" citation
  exactly as the docs do.
\<close>

lemma beta_step_is_beta_sigma_step: "M \<rightarrow>\<beta> N \<Longrightarrow> M \<rightarrow>\<beta>\<sigma> N"
proof (induction rule: beta_step.induct)
  case (Beta x M N)
  then show ?case by (simp add: beta_sigma_step.Beta)
next
  case (BetaClos x M L N)
  then show ?case by (simp add: beta_sigma_step.BetaClos)
next
  case (CompEps M N)
  then show ?case by (simp add: beta_sigma_step.CompEps)
qed (blast intro: beta_sigma_step.intros)+

lemma beta_over_sigma_step_is_beta_sigma_steps:
  assumes "U \<rightarrow>\<beta>\<bar>\<sigma> V"
  shows "U \<rightarrow>\<beta>\<sigma>\<^sup>* V"
proof -
  from assms obtain M where M: "U \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* V"
    by (auto simp: beta_over_sigma_step_def)
  have "U \<rightarrow>\<beta>\<sigma> M" using M(1) by (rule beta_step_is_beta_sigma_step)
  moreover have "M \<rightarrow>\<beta>\<sigma>\<^sup>* V"
    using M(2)
    by (induction rule: rtranclp.induct)
       (auto intro: sigma_step_is_beta_sigma_step rtranclp.rtrancl_into_rtrancl)
  ultimately show ?thesis by (rule converse_rtranclp_into_rtranclp)
qed

lemma beta_over_sigma_steps_are_beta_sigma_steps:
  assumes "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* V"
  shows "U \<rightarrow>\<beta>\<sigma>\<^sup>* V"
  using assms
  by (induction rule: rtranclp.induct)
     (auto dest: beta_over_sigma_step_is_beta_sigma_steps intro: rtranclp_trans)

lemma sigma_nf_reachable_by_beta_sigma: "M \<rightarrow>\<beta>\<sigma>\<^sup>* sigma_nf M"
  using sigma_nf_reduces
  by (induction rule: rtranclp.induct) (auto intro: sigma_step_is_beta_sigma_step rtranclp.rtrancl_into_rtrancl)

text \<open>Fact: lifting an arbitrary @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>\<^sup>*"} reduction to
      @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} between @{text "\<sigma>"}-normal forms.\<close>

lemma beta_sigma_steps_lifted_to_beta_over_sigma:
  assumes "P \<rightarrow>\<beta>\<sigma>\<^sup>* Q"
  shows "sigma_nf P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf Q"
  using assms
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl P)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl P P\<^sub>1 Q)
  from beta_sigma_step_iff_beta_or_sigma [THEN iffD1, OF \<open>P\<^sub>1 \<rightarrow>\<beta>\<sigma> Q\<close>]
  consider (b) "P\<^sub>1 \<rightarrow>\<beta> Q" | (s) "P\<^sub>1 \<rightarrow>\<sigma> Q" by blast
  then show ?case
  proof cases
    case b
    have "sigma_nf P\<^sub>1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf Q"
      using beta_step_simulated_by_beta_over_sigma [OF b] by simp
    with rtrancl_into_rtrancl.IH show ?thesis by (rule rtranclp_trans)
  next
    case s
    then have "sigma_nf P\<^sub>1 = sigma_nf Q" by (rule sigma_step_preserves_sigma_nf)
    with rtrancl_into_rtrancl.IH show ?thesis by simp
  qed
qed

theorem beta_sigma_confluent:
  assumes "M \<rightarrow>\<beta>\<sigma>\<^sup>* N\<^sub>1" and "M \<rightarrow>\<beta>\<sigma>\<^sup>* N\<^sub>2"
  shows "\<exists>L. N\<^sub>1 \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
proof -
  have f1: "sigma_nf M \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf N\<^sub>1"
    using beta_sigma_steps_lifted_to_beta_over_sigma [OF assms(1)] .
  have f2: "sigma_nf M \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf N\<^sub>2"
    using beta_sigma_steps_lifted_to_beta_over_sigma [OF assms(2)] .
  have nf_M: "is_sigma_normal (sigma_nf M)"
    using sigma_nf_irreducible [of M] by (simp add: sigma_normal_form_grammar)
  obtain L where L: "sigma_nf N\<^sub>1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* L" "sigma_nf N\<^sub>2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* L"
    using beta_over_sigma_confluent [OF nf_M f1 f2] by blast
  have "N\<^sub>1 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
    using sigma_nf_reachable_by_beta_sigma [of N\<^sub>1]
          beta_over_sigma_steps_are_beta_sigma_steps [OF L(1)]
    by (rule rtranclp_trans)
  moreover have "N\<^sub>2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
    using sigma_nf_reachable_by_beta_sigma [of N\<^sub>2]
          beta_over_sigma_steps_are_beta_sigma_steps [OF L(2)]
    by (rule rtranclp_trans)
  ultimately show ?thesis by blast
qed

end
