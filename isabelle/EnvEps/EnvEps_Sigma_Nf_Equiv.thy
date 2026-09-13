theory EnvEps_Sigma_Nf_Equiv
  imports EnvEps_Sigma_Normal_Form_Grammar EnvEps_Sigma_Congruence
begin

text \<open>
  Equational facts about @{text sigma_nf}, used throughout
  @{text EnvEps_Parallel_Reduction_Composition_Compatibility} (roadmap
  22) to rewrite both sides of the goal into a common shape without
  re-deriving termination/confluence arguments at every step.

  The first four ("safe context") lemmas are the formal counterpart of
  the informal Fact used in @{text EnvEps_Beta_Normal_Form_Simulation}
  and @{text EnvEps_Parallel_Reduction_Soundness}: @{text Lam}, @{text
  Eps}, @{text App}, @{text Ext} are never themselves @{text "\<sigma>"}-redex
  sites, so normalizing commutes with them. The remaining lemmas compute
  @{text "sigma_nf (Comp \<dots>)"} one @{text "\<rightarrow>\<sigma>"} base rule at a time, by
  taking that single step (invariant under @{text sigma_nf} by
  @{text sigma_step_preserves_sigma_nf}) and then, where the result is
  itself a safe-context node, applying the corresponding safe-context
  lemma.
\<close>

lemma sigma_nf_Lam: "sigma_nf (Lam x P) = Lam x (sigma_nf P)"
proof (rule sigma_nf_eq_if_reduces_and_irreducible)
  show "Lam x P \<rightarrow>\<sigma>\<^sup>* Lam x (sigma_nf P)" by (rule sigma_steps_Lam) simp
  show "sigma_irreducible (Lam x (sigma_nf P))"
    using is_sigma_normal.NF_Lam [OF is_sigma_normal_sigma_nf]
    by (simp add: sigma_normal_form_grammar [symmetric])
qed

lemma sigma_nf_Eps: "sigma_nf (Eps P) = Eps (sigma_nf P)"
proof (rule sigma_nf_eq_if_reduces_and_irreducible)
  show "Eps P \<rightarrow>\<sigma>\<^sup>* Eps (sigma_nf P)" by (rule sigma_steps_Eop) simp
  show "sigma_irreducible (Eps (sigma_nf P))"
    using is_sigma_normal.NF_Eps [OF is_sigma_normal_sigma_nf]
    by (simp add: sigma_normal_form_grammar [symmetric])
qed

lemma sigma_nf_App: "sigma_nf (App P Q) = App (sigma_nf P) (sigma_nf Q)"
proof (rule sigma_nf_eq_if_reduces_and_irreducible)
  show "App P Q \<rightarrow>\<sigma>\<^sup>* App (sigma_nf P) (sigma_nf Q)" by (rule sigma_steps_App) simp_all
  show "sigma_irreducible (App (sigma_nf P) (sigma_nf Q))"
    using is_sigma_normal.NF_App [OF is_sigma_normal_sigma_nf is_sigma_normal_sigma_nf]
    by (simp add: sigma_normal_form_grammar [symmetric])
qed

lemma sigma_nf_Ext: "sigma_nf (Ext P x Q) = Ext (sigma_nf P) x (sigma_nf Q)"
proof (rule sigma_nf_eq_if_reduces_and_irreducible)
  show "Ext P x Q \<rightarrow>\<sigma>\<^sup>* Ext (sigma_nf P) x (sigma_nf Q)" by (rule sigma_steps_Ext) simp_all
  show "sigma_irreducible (Ext (sigma_nf P) x (sigma_nf Q))"
    using is_sigma_normal.NF_Ext [OF is_sigma_normal_sigma_nf is_sigma_normal_sigma_nf]
    by (simp add: sigma_normal_form_grammar [symmetric])
qed

lemma sigma_nf_Comp_Assoc:
  "sigma_nf (Comp (Comp A B) C) = sigma_nf (Comp A (Comp B C))"
  by (rule sigma_step_preserves_sigma_nf [OF sigma_step.Assoc])

lemma sigma_nf_Comp_IdL: "sigma_nf (Comp Id C) = sigma_nf C"
  by (rule sigma_step_preserves_sigma_nf [OF sigma_step.IdL])

lemma sigma_nf_Comp_IdR: "sigma_nf (Comp C Id) = sigma_nf C"
  by (rule sigma_step_preserves_sigma_nf [OF sigma_step.IdR])

lemma sigma_nf_Comp_Ext:
  "sigma_nf (Comp (Ext A x B) C) = Ext (sigma_nf (Comp A C)) x (sigma_nf (Comp B C))"
  using sigma_step_preserves_sigma_nf [OF sigma_step.DExtn, of A x B C]
  by (simp add: sigma_nf_Ext)

lemma sigma_nf_Comp_App:
  "sigma_nf (Comp (App A B) C) = App (sigma_nf (Comp A C)) (sigma_nf (Comp B C))"
  using sigma_step_preserves_sigma_nf [OF sigma_step.DApp, of A B C]
  by (simp add: sigma_nf_App)

lemma sigma_nf_Comp_Eps: "sigma_nf (Comp (Eps A) C) = Eps (sigma_nf A)"
  using sigma_step_preserves_sigma_nf [OF sigma_step.EpsEps, of A C]
  by (simp add: sigma_nf_Eps)

lemma sigma_nf_Comp_VarRef: "sigma_nf (Comp (Var x) (Ext A x B)) = sigma_nf A"
  by (rule sigma_step_preserves_sigma_nf [OF sigma_step.VarRef])

lemma sigma_nf_Comp_VarSkip:
  "x \<noteq> y \<Longrightarrow> sigma_nf (Comp (Var x) (Ext A y B)) = sigma_nf (Comp (Var x) B)"
  by (rule sigma_step_preserves_sigma_nf [OF sigma_step.VarSkip])

text \<open>
  When @{text U} and @{text V} are themselves @{text "\<sigma>"}-normal and match
  one of the two @{text Comp}-shaped grammar productions, @{term "Comp U V"}
  is already @{text "\<sigma>"}-normal, so @{text sigma_nf} is a no-op on it.
\<close>

lemma sigma_nf_of_normal [simp]: "is_sigma_normal M \<Longrightarrow> sigma_nf M = M"
  using sigma_normal_form_grammar [of M]
  by (intro sigma_nf_eq_if_reduces_and_irreducible [OF rtranclp.rtrancl_refl]) simp

text \<open>
  Idempotence: normalizing a component of a @{text Comp} node before
  composing does not change the overall @{text sigma_nf}. Used to justify
  routing through an already-computed @{text sigma_nf} of a subterm when
  re-composing it with something else (e.g. the @{text ParBeta} /
  @{text ParBetaClos} cases of
  @{text EnvEps_Parallel_Reduction_Composition_Compatibility}).
\<close>

lemma sigma_nf_Comp_idem_L: "sigma_nf (Comp A B) = sigma_nf (Comp (sigma_nf A) B)"
  using sigma_steps_CompL [OF sigma_nf_reduces, of A B]
  by (rule sigma_steps_preserve_sigma_nf)

lemma sigma_nf_Comp_idem_R: "sigma_nf (Comp A B) = sigma_nf (Comp A (sigma_nf B))"
proof (rule sigma_steps_preserve_sigma_nf)
  show "Comp A B \<rightarrow>\<sigma>\<^sup>* Comp A (sigma_nf B)"
    by (rule sigma_steps_CompR) simp
qed

text \<open>
  @{text length_enve} never increases under @{text sigma_nf}: it is a
  non-strict weakening of @{text sigma_step_length_decrease}, obtained by
  summing the (possibly zero) strict decreases along the reduction to
  normal form.
\<close>

text \<open>
  Composing with a fixed @{term V} preserves strict length ordering: this
  reduces every length inequality needed by
  @{text EnvEps_Parallel_Reduction_Composition_Compatibility} to a
  @{text V}-independent inequality about @{text length_enve} of the
  relevant subterms of @{text U} alone.
\<close>

lemma length_enve_Comp_mono:
  assumes "length_enve X < length_enve Y"
  shows "length_enve (Comp X V) < length_enve (Comp Y V)"
proof -
  have "length_enve X * (length_enve V + 1) < length_enve Y * (length_enve V + 1)"
    using assms by (rule mult_strict_right_mono) simp
  then show ?thesis by simp
qed

lemma length_enve_sigma_nf_le: "length_enve (sigma_nf M) \<le> length_enve M"
proof -
  have "M \<rightarrow>\<sigma>\<^sup>* sigma_nf M" by simp
  then show ?thesis
    by (induction rule: rtranclp.induct) (auto dest: sigma_step_length_decrease)
qed

end
