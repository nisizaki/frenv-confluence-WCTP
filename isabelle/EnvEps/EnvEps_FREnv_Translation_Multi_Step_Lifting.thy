theory EnvEps_FREnv_Translation_Multi_Step_Lifting
  imports EnvEps_FREnv_Translation_Lifting EnvEps_Beta_Sigma_Full_Confluence
begin

text \<open>
  Multi-step lifting lemma (docs file
  @{text "docs/enve-frenv-translation-multi-step-lifting.md"}, thesis
  Lemma 4; roadmap item 31): generalizes the Single-Step Lifting Lemma
  (@{text translate_single_step_lifting}) from one @{text "lambda_FREnv"}
  -side step to an arbitrary chain, by induction on chain length,
  repeatedly reconciling each new witness against everything found so far
  using confluence of @{text "lambda_EnvEps"}'s own @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"}.

  \<^bold>\<open>Difference from the docs.\<close> The docs state this lemma \<^emph>\<open>conditionally\<close>,
  carrying that confluence as an explicit hypothesis, because at the
  corresponding point of the thesis confluence had not yet been proved --
  while noting that the condition "is now dischargeable via Theorem 13".
  Here it \<^emph>\<open>is\<close> discharged: this theory imports
  @{text EnvEps_Beta_Sigma_Full_Confluence} (roadmap item 26, thesis
  Theorem 13) and states the lemma unconditionally. Besides matching how
  the result is actually used, this avoids carrying an assumption that is
  itself a @{text "\<And>"}-quantified rule with an existential conclusion,
  which resolves only by higher-order unification and so is awkward to
  discharge at every use site.

  Single-step lifting is proved in the imported theory, including both
  BetaClos preimage shapes.
\<close>

theorem translate_multi_step_lifting:
  assumes chain: "FREnv_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* \<lbrakk>M\<rbrakk> N'"
  shows "\<exists>N L. \<lbrakk>N\<rbrakk> = N'
           \<and> EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N L
           \<and> EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L"
  using chain
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (intro exI [of _ M] exI [of _ M]) simp
next
  case (step N0 N1)
  from step.IH obtain N L
    where Neq: "\<lbrakk>N\<rbrakk> = N0" and NL: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N L"
      and MLfact: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L"
    by blast
  have Nstep: "\<lbrakk>N\<rbrakk> \<rightarrow>F N1" using step.hyps(2) Neq by simp
  from translate_single_step_lifting [OF Nstep] obtain N2 L2
    where N2eq: "\<lbrakk>N2\<rbrakk> = N1"
      and N2L2: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N2 L2"
      and NL2: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N L2"
    by blast
  from beta_sigma_confluent [OF NL NL2] obtain L3
    where LL3: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* L L3"
      and L2L3: "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* L2 L3"
    by blast
  have "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N2 L3"
    using N2L2 L2L3 by (rule rtranclp_trans)
  moreover have "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L3"
    using MLfact LL3 by (rule rtranclp_trans)
  ultimately show ?case using N2eq by blast
qed

end
