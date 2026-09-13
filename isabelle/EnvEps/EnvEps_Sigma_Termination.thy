theory EnvEps_Sigma_Termination
  imports EnvEps_Sigma_Length_Decrease
begin

text \<open>
  Termination (strong normalization) of @{text "\<rightarrow>\<sigma>"} (docs file
  @{text "docs/enve-sigma-reduction-termination.md"}, thesis Theorem 4),
  derived from the Length Decrease Lemma
  (@{text "EnvEps_Sigma_Length_Decrease.sigma_step_length_decrease"}) via
  well-foundedness of @{text length_enve} as a measure.
\<close>

lemma sigma_step_wf: "wf {(N, M). M \<rightarrow>\<sigma> N}"
proof (rule wf_subset)
  show "wf (measure length_enve)" by simp
  show "{(N, M). M \<rightarrow>\<sigma> N} \<subseteq> measure length_enve"
    by (auto dest: sigma_step_length_decrease)
qed

theorem sigma_reduction_terminating:
  "\<nexists>f. \<forall>i. f i \<rightarrow>\<sigma> f (Suc i)"
proof
  assume "\<exists>f. \<forall>i. f i \<rightarrow>\<sigma> f (Suc i)"
  then obtain f where f: "\<forall>i. f i \<rightarrow>\<sigma> f (Suc i)" ..
  have "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(N, M). M \<rightarrow>\<sigma> N}"
    by (rule exI [of _ f]) (use f in simp)
  with sigma_step_wf wf_iff_no_infinite_down_chain show False by blast
qed

end
