theory EnvEps_Beta_Over_Sigma_Confluence
  imports EnvEps_Parallel_Reduction_Confluence EnvEps_Parallel_Reduction_Simulation
    EnvEps_Parallel_Reduction_Soundness
begin

text \<open>
  Confluence of @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"} (docs file
  @{text "docs/enve-beta-over-sigma-confluence.md"}, thesis Theorem 12;
  roadmap item 25), assembled from confluence of @{text "\<Rightarrow>par"}
  (@{text par_step_confluent}) plus the multi-step versions of the
  Simulation and Soundness lemmas (Facts 1 and 2 of the docs).

  Both multi-step liftings are proved here in full, by chain-length
  induction; the @{text is_sigma_normal} hypothesis each single-step
  lemma needs at every intermediate term is supplied by the preservation
  lemmas @{text beta_over_sigma_steps_target_normal} and
  @{text par_step_target_normal}. This theory therefore introduces no
  gap of its own; it inherits only those of the two single-step lemmas
  (roadmap 19 and 20) and of @{text par_step_triangle} (roadmap 23,
  which in turn rests on roadmap 22).
\<close>

lemma beta_over_sigma_steps_simulated_by_par_steps:
  assumes "is_sigma_normal P" and "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Q"
  shows "P \<Rightarrow>par\<^sup>* Q"
  using assms(2) assms(1)
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl P)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl P Q\<^sub>1 Q)
  then have par1: "P \<Rightarrow>par\<^sup>* Q\<^sub>1" by simp
  have "is_sigma_normal Q\<^sub>1"
    using rtrancl_into_rtrancl.prems rtrancl_into_rtrancl.hyps(1)
    by (rule beta_over_sigma_steps_target_normal)
  from beta_over_sigma_step_simulated_by_par_step [OF this rtrancl_into_rtrancl.hyps(2)]
  have "Q\<^sub>1 \<Rightarrow>par Q" .
  with par1 show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma par_steps_sound_for_beta_over_sigma:
  assumes "is_sigma_normal P" and "P \<Rightarrow>par\<^sup>* Q"
  shows "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Q"
  using assms(2) assms(1)
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl P)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl P Q\<^sub>1 Q)
  then have steps1: "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Q\<^sub>1" by simp
  have "is_sigma_normal Q\<^sub>1"
    using rtrancl_into_rtrancl.prems rtrancl_into_rtrancl.hyps(1)
    by (rule par_steps_target_normal)
  from par_step_sound_for_beta_over_sigma [OF this rtrancl_into_rtrancl.hyps(2)]
  have "Q\<^sub>1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Q" .
  with steps1 show ?case by (rule rtranclp_trans)
qed

theorem beta_over_sigma_confluent:
  assumes "is_sigma_normal U" and "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>1" and "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>2"
  shows "\<exists>U\<^sub>3. U\<^sub>1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>3 \<and> U\<^sub>2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>3"
proof -
  have par1: "U \<Rightarrow>par\<^sup>* U\<^sub>1"
    using assms(1) assms(2) by (rule beta_over_sigma_steps_simulated_by_par_steps)
  have par2: "U \<Rightarrow>par\<^sup>* U\<^sub>2"
    using assms(1) assms(3) by (rule beta_over_sigma_steps_simulated_by_par_steps)
  obtain U\<^sub>3 where U3: "U\<^sub>1 \<Rightarrow>par\<^sup>* U\<^sub>3" "U\<^sub>2 \<Rightarrow>par\<^sup>* U\<^sub>3"
    using par_step_confluent [OF par1 par2] by blast
  have n1: "is_sigma_normal U\<^sub>1" using assms(1) assms(2) by (rule beta_over_sigma_steps_target_normal)
  have n2: "is_sigma_normal U\<^sub>2" using assms(1) assms(3) by (rule beta_over_sigma_steps_target_normal)
  have "U\<^sub>1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>3" using n1 U3(1) by (rule par_steps_sound_for_beta_over_sigma)
  moreover have "U\<^sub>2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U\<^sub>3" using n2 U3(2) by (rule par_steps_sound_for_beta_over_sigma)
  ultimately show ?thesis by blast
qed

end
