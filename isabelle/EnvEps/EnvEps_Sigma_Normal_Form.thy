theory EnvEps_Sigma_Normal_Form
  imports EnvEps_Sigma_Confluence
begin

text \<open>
  @{text "\<sigma>"}-normal forms on @{text "lambda_EnvEps"} (docs file
  @{text "docs/enve-sigma-normal-form.md"}, thesis Definition 12; roadmap
  item 13). Depends on termination (existence) and confluence
  (uniqueness) of @{text "\<rightarrow>\<sigma>"}, both of which are fully proved
  (@{text EnvEps_Sigma_Termination}, @{text EnvEps_Sigma_Confluence}), so
  the well-definedness results below are unconditional.
\<close>

definition sigma_irreducible :: "trm \<Rightarrow> bool" where
  "sigma_irreducible N \<longleftrightarrow> (\<nexists>N'. N \<rightarrow>\<sigma> N')"

lemma sigma_irreducible_no_step [dest]:
  "sigma_irreducible N \<Longrightarrow> N \<rightarrow>\<sigma> N' \<Longrightarrow> False"
  by (simp add: sigma_irreducible_def)

text \<open>Existence: every term reaches a @{text "\<sigma>"}-irreducible term.\<close>

lemma sigma_nf_exists: "\<exists>N. M \<rightarrow>\<sigma>\<^sup>* N \<and> sigma_irreducible N"
proof (induction M rule: wf_induct_rule [OF sigma_step_wf])
  case (1 x)
  show ?case
  proof (cases "sigma_irreducible x")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain x' where "x \<rightarrow>\<sigma> x'" by (auto simp: sigma_irreducible_def)
    then have "(x', x) \<in> {(N, M). M \<rightarrow>\<sigma> N}" by simp
    with "1.IH" obtain N where "x' \<rightarrow>\<sigma>\<^sup>* N" "sigma_irreducible N" by blast
    with \<open>x \<rightarrow>\<sigma> x'\<close> show ?thesis by (auto intro: converse_rtranclp_into_rtranclp)
  qed
qed

text \<open>Uniqueness: any two @{text "\<sigma>"}-irreducible terms reachable from the
      same @{term M} coincide.\<close>

lemma sigma_irreducible_reachable_eq:
  assumes "sigma_irreducible N" and "N \<rightarrow>\<sigma>\<^sup>* L"
  shows "N = L"
  using assms(2) assms(1)
  by (induction rule: rtranclp.induct) (auto simp: sigma_irreducible_def)

lemma sigma_nf_unique:
  assumes "M \<rightarrow>\<sigma>\<^sup>* N" and "sigma_irreducible N"
    and "M \<rightarrow>\<sigma>\<^sup>* N'" and "sigma_irreducible N'"
  shows "N = N'"
proof -
  obtain L where L: "N \<rightarrow>\<sigma>\<^sup>* L" "N' \<rightarrow>\<sigma>\<^sup>* L"
    using sigma_confluent [OF assms(1) assms(3)] by blast
  from sigma_irreducible_reachable_eq [OF assms(2) L(1)]
       sigma_irreducible_reachable_eq [OF assms(4) L(2)]
  show ?thesis by simp
qed

text \<open>The @{text "\<sigma>"}-normal form itself, @{term "\<sigma>(M)"} in the docs.\<close>

definition sigma_nf :: "trm \<Rightarrow> trm" where
  "sigma_nf M = (SOME N. M \<rightarrow>\<sigma>\<^sup>* N \<and> sigma_irreducible N)"

lemma sigma_nf_spec: "M \<rightarrow>\<sigma>\<^sup>* sigma_nf M \<and> sigma_irreducible (sigma_nf M)"
  unfolding sigma_nf_def by (rule someI_ex) (rule sigma_nf_exists)

lemma sigma_nf_reduces [simp]: "M \<rightarrow>\<sigma>\<^sup>* sigma_nf M"
  using sigma_nf_spec by blast

lemma sigma_nf_irreducible [simp]: "sigma_irreducible (sigma_nf M)"
  using sigma_nf_spec by blast

lemma sigma_nf_eq_if_reduces_and_irreducible:
  assumes "M \<rightarrow>\<sigma>\<^sup>* N" and "sigma_irreducible N"
  shows "sigma_nf M = N"
  using sigma_nf_unique [OF sigma_nf_reduces sigma_nf_irreducible assms(1) assms(2)] .

text \<open>
  @{text "\<sigma>"}-reduction never changes a term's (unique) @{text "\<sigma>"}-normal
  form. Used by @{text EnvEps_Beta_Sigma_Full_Confluence} (roadmap 26).
\<close>

lemma sigma_steps_preserve_sigma_nf:
  assumes "P \<rightarrow>\<sigma>\<^sup>* Q"
  shows "sigma_nf P = sigma_nf Q"
proof -
  have "P \<rightarrow>\<sigma>\<^sup>* sigma_nf Q"
    using assms sigma_nf_reduces by (rule rtranclp_trans)
  then show ?thesis
    using sigma_nf_irreducible by (rule sigma_nf_eq_if_reduces_and_irreducible)
qed

lemma sigma_step_preserves_sigma_nf:
  assumes "P \<rightarrow>\<sigma> Q"
  shows "sigma_nf P = sigma_nf Q"
  using assms by (intro sigma_steps_preserve_sigma_nf) auto

text \<open>Equivalent characterization: @{term N} is a @{text "\<sigma>"}-normal form
      (i.e. @{text "N = \<sigma>(L)"} for some @{term L}) iff @{term N} is
      @{text "\<sigma>"}-irreducible.\<close>

lemma is_sigma_normal_form_iff_irreducible:
  "(\<exists>L. N = sigma_nf L) \<longleftrightarrow> sigma_irreducible N"
proof
  assume "\<exists>L. N = sigma_nf L"
  then show "sigma_irreducible N" using sigma_nf_irreducible by blast
next
  assume "sigma_irreducible N"
  then have "sigma_nf N = N"
    by (rule sigma_nf_eq_if_reduces_and_irreducible [OF rtranclp.rtrancl_refl])
  then show "\<exists>L. N = sigma_nf L" by (intro exI [of _ N]) simp
qed

end
