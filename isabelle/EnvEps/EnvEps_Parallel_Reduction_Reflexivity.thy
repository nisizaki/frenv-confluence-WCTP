theory EnvEps_Parallel_Reduction_Reflexivity
  imports EnvEps_Parallel_Reduction
begin

text \<open>
  Reflexivity of @{text "\<Rightarrow>par"} on @{text "\<sigma>"}-normal forms (docs file
  @{text "docs/enve-parallel-reduction-reflexivity.md"}, thesis Lemma 6;
  roadmap item 18).
\<close>

lemma sigma_nf_of_irreducible [simp]: "sigma_irreducible U \<Longrightarrow> sigma_nf U = U"
  by (rule sigma_nf_eq_if_reduces_and_irreducible [OF rtranclp.rtrancl_refl])

theorem par_step_refl:
  assumes "is_sigma_normal U"
  shows "U \<Rightarrow>par U"
  using assms
proof (induction rule: is_sigma_normal.induct)
  case NF_Id
  then show ?case by (simp add: par_step.ParId)
next
  case (NF_Var x)
  then show ?case by (simp add: par_step.ParVar)
next
  case (NF_Lam U x)
  then show ?case by (simp add: par_step.ParLam)
next
  case (NF_App U1 U2)
  then show ?case by (simp add: par_step.ParApp)
next
  case (NF_Ext U1 U2 x)
  then show ?case by (simp add: par_step.ParExtn)
next
  case (NF_Eps U)
  then show ?case by (simp add: par_step.ParEps)
next
  case (NF_CompLam U1 U3 x)
  then have "Comp (Lam x U1) U3 \<Rightarrow>par sigma_nf (Comp (Lam x U1) U3)"
    by (intro par_step.ParLamComp) auto
  moreover have "sigma_irreducible (Comp (Lam x U1) U3)"
    using is_sigma_normal.NF_CompLam [OF NF_CompLam.hyps(1,2,3)]
    by (simp add: sigma_normal_form_grammar)
  ultimately show ?case by simp
next
  case (NF_CompVar W x)
  then have "Comp (Var x) W \<Rightarrow>par sigma_nf (Comp (Var x) W)"
    by (intro par_step.ParVarComp) auto
  moreover have "sigma_irreducible (Comp (Var x) W)"
    using is_sigma_normal.NF_CompVar [OF NF_CompVar.hyps(1,2,3)]
    by (simp add: sigma_normal_form_grammar)
  ultimately show ?case by simp
qed

text \<open>
  @{text "\<Rightarrow>par"} relates only @{text "\<sigma>"}-normal forms, in both
  directions. Together with @{text par_step_refl} this pins down its
  domain exactly as the docs describe it, and (crucially) lets the
  diamond property be stated unconditionally in
  @{text EnvEps_Parallel_Reduction_Confluence}: the
  @{text is_sigma_normal} hypothesis of the triangle property becomes
  derivable from the reduction step itself.
\<close>

lemma par_step_source_normal:
  assumes "U \<Rightarrow>par V"
  shows "is_sigma_normal U"
  using assms
  by (induction rule: par_step.induct)
     (auto intro: is_sigma_normal.intros)

lemma par_step_target_normal:
  assumes "U \<Rightarrow>par V"
  shows "is_sigma_normal V"
  using assms
  by (induction rule: par_step.induct)
     (auto intro: is_sigma_normal.intros)

lemma par_steps_target_normal:
  assumes "is_sigma_normal U" and "U \<Rightarrow>par\<^sup>* V"
  shows "is_sigma_normal V"
  using assms(2) assms(1)
  by (induction rule: rtranclp.induct) (auto dest: par_step_target_normal)

end
