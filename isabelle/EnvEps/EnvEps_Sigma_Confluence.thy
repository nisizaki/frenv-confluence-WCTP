theory EnvEps_Sigma_Confluence
  imports EnvEps_Sigma_Termination EnvEps_Sigma_Local_Confluence Newmans_Lemma
begin

text \<open>
  Confluence of @{text "\<rightarrow>\<sigma>"} on @{text "lambda_EnvEps"} (docs file
  @{text "docs/enve-sigma-reduction-confluence.md"}, thesis Theorem 5;
  roadmap item 12), obtained from termination
  (@{text "EnvEps_Sigma_Termination.sigma_step_wf"}) and local confluence
  (@{text "EnvEps_Sigma_Local_Confluence.sigma_locally_confluent"}) via
  the generic @{text "Newmans_Lemma.newmans_lemma"}.

  Both ingredients are now fully proved -- termination in
  @{text EnvEps_Sigma_Termination} and local confluence in
  @{text EnvEps_Sigma_Local_Confluence} -- so this theorem is
  unconditional: it depends on no unproved lemma.
\<close>

theorem sigma_confluent:
  assumes "M \<rightarrow>\<sigma>\<^sup>* N\<^sub>1" and "M \<rightarrow>\<sigma>\<^sup>* N\<^sub>2"
  shows "\<exists>L. N\<^sub>1 \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using newmans_lemma [OF sigma_step_wf sigma_locally_confluent assms(1) assms(2)] .

end
