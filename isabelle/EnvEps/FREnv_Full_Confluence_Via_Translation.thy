theory FREnv_Full_Confluence_Via_Translation
  imports EnvEps_FREnv_Translation_Multi_Step_Lifting
    EnvEps_FREnv_Translation_Surjective EnvEps_Beta_Sigma_Full_Confluence
begin

text \<open>
  Confluence of @{text "lambda_FREnv"}'s full @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} on all terms
  (docs file @{text "docs/frenv-beta-sigma-full-confluence.md"}, thesis
  Theorem 14; roadmap item 32, the final item of the roadmap).

  Assembled exactly as the docs do -- bypassing the thesis's
  unrecoverable "Theorem 2" citation -- from four ingredients:

    \<^item> surjectivity of @{text "\<lbrakk>-\<rbrakk>"}
      (@{text translate_surjective}, roadmap 28, fully proved),
    \<^item> the multi-step simulation
      (@{text translate_simulates_beta_sigma_steps}, roadmap 29, fully
      proved),
    \<^item> the Multi-Step Lifting Lemma
      (@{text translate_multi_step_lifting}, roadmap 31, stated there
      unconditionally, its confluence hypothesis already discharged), and
    \<^item> confluence of @{text "lambda_EnvEps"}
      (@{text EnvEps_Beta_Sigma_Full_Confluence.beta_sigma_confluent},
      roadmap 26), used here to join the two lifted endpoints.

  Given @{text "P \<rightarrow>\<^sup>* Q\<^sub>1"} and @{text "P \<rightarrow>\<^sup>* Q\<^sub>2"} in @{text "lambda_FREnv"},
  pick @{term M} with @{term "\<lbrakk>M\<rbrakk> = P"}, lift both chains back to
  @{text "lambda_EnvEps"}, join them there, and push the join forward
  again through @{text "\<lbrakk>-\<rbrakk>"}; the common reduct is the translation of
  the @{text "lambda_EnvEps"}-side join.

  The theorem below transfers confluence through the translation.
  Its imported ingredients are included in this artifact and are checked
  with quick_and_dirty disabled.
\<close>

theorem frenv_beta_sigma_confluent:
  assumes "P \<rightarrow>F\<^sup>* Q\<^sub>1" and "P \<rightarrow>F\<^sup>* Q\<^sub>2"
  shows "\<exists>L. Q\<^sub>1 \<rightarrow>F\<^sup>* L \<and> Q\<^sub>2 \<rightarrow>F\<^sup>* L"
proof -
  obtain M where M: "\<lbrakk>M\<rbrakk> = P" using translate_surjective by blast
  have c1: "\<lbrakk>M\<rbrakk> \<rightarrow>F\<^sup>* Q\<^sub>1" using assms(1) M by simp
  have c2: "\<lbrakk>M\<rbrakk> \<rightarrow>F\<^sup>* Q\<^sub>2" using assms(2) M by simp
  \<comment> \<open>Lift each @{text "lambda_FREnv"} chain back to @{text "lambda_EnvEps"}.\<close>
  obtain N\<^sub>1 L\<^sub>1 where one: "\<lbrakk>N\<^sub>1\<rbrakk> = Q\<^sub>1"
      "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N\<^sub>1 L\<^sub>1"
      "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L\<^sub>1"
    using translate_multi_step_lifting [OF c1] by blast
  obtain N\<^sub>2 L\<^sub>2 where two: "\<lbrakk>N\<^sub>2\<rbrakk> = Q\<^sub>2"
      "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N\<^sub>2 L\<^sub>2"
      "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L\<^sub>2"
    using translate_multi_step_lifting [OF c2] by blast
  \<comment> \<open>Join the two lifted endpoints on the @{text "lambda_EnvEps"} side.\<close>
  obtain L where L: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* L\<^sub>1 L"
      "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* L\<^sub>2 L"
    using beta_sigma_confluent [OF one(3) two(3)] by blast
  have e1: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N\<^sub>1 L"
    using one(2) L(1) by (rule rtranclp_trans)
  have e2: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N\<^sub>2 L"
    using two(2) L(2) by (rule rtranclp_trans)
  \<comment> \<open>Push the join forward again through the translation.\<close>
  have "Q\<^sub>1 \<rightarrow>F\<^sup>* \<lbrakk>L\<rbrakk>"
    using translate_simulates_beta_sigma_steps [OF e1] one(1) by simp
  moreover have "Q\<^sub>2 \<rightarrow>F\<^sup>* \<lbrakk>L\<rbrakk>"
    using translate_simulates_beta_sigma_steps [OF e2] two(1) by simp
  ultimately show ?thesis by blast
qed

end
