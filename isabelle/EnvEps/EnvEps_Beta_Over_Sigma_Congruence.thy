theory EnvEps_Beta_Over_Sigma_Congruence
  imports EnvEps_Beta_Over_Sigma EnvEps_Sigma_Congruence
begin

lemma sigma_nf_of_irreducible [simp]: "sigma_irreducible U \<Longrightarrow> sigma_nf U = U"
  by (rule sigma_nf_eq_if_reduces_and_irreducible [OF rtranclp.rtrancl_refl])

text \<open>
  Context monotonicity of @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} through the four "safe" constructors
  @{text Lam}, @{text Eps}, @{text App}, @{text Ext} -- none of which is
  ever itself a @{text "\<sigma>"}-redex, so @{text "\<sigma>"}-normalization commutes
  with them. Needed by @{text EnvEps_Parallel_Reduction_Soundness}
  (roadmap item 20, the "Fact" of its docs).
\<close>

lemma beta_over_sigma_step_Lam:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'"
  shows "Lam x P \<rightarrow>\<beta>\<bar>\<sigma> Lam x P'"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms by (auto simp: beta_over_sigma_step_def)
  have "Lam x P \<rightarrow>\<beta> Lam x M" using M(1) by (rule EnvEps_Beta_Step.beta_step.Lam)
  moreover have "Lam x M \<rightarrow>\<sigma>\<^sup>* Lam x P'" using M(2) by (rule sigma_steps_Lam)
  moreover have "is_sigma_normal (Lam x P')" using M(3) by (rule is_sigma_normal.NF_Lam)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_Eps:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'"
  shows "Eps P \<rightarrow>\<beta>\<bar>\<sigma> Eps P'"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms by (auto simp: beta_over_sigma_step_def)
  have "Eps P \<rightarrow>\<beta> Eps M" using M(1) by (rule EnvEps_Beta_Step.beta_step.Eop)
  moreover have "Eps M \<rightarrow>\<sigma>\<^sup>* Eps P'" using M(2) by (rule sigma_steps_Eop)
  moreover have "is_sigma_normal (Eps P')" using M(3) by (rule is_sigma_normal.NF_Eps)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_AppL:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q"
  shows "App P Q \<rightarrow>\<beta>\<bar>\<sigma> App P' Q"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have "App P Q \<rightarrow>\<beta> App M Q" using M(1) by (rule EnvEps_Beta_Step.beta_step.AppL)
  moreover have "App M Q \<rightarrow>\<sigma>\<^sup>* App P' Q" using M(2) by (rule sigma_steps_AppL)
  moreover have "is_sigma_normal (App P' Q)"
    using M(3) assms(2) by (rule is_sigma_normal.NF_App)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_AppR:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q"
  shows "App Q P \<rightarrow>\<beta>\<bar>\<sigma> App Q P'"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have "App Q P \<rightarrow>\<beta> App Q M" using M(1) by (rule EnvEps_Beta_Step.beta_step.AppR)
  moreover have "App Q M \<rightarrow>\<sigma>\<^sup>* App Q P'" using M(2) by (rule sigma_steps_AppR)
  moreover have "is_sigma_normal (App Q P')"
    using assms(2) M(3) by (rule is_sigma_normal.NF_App)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_ExtnL:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q"
  shows "Ext P x Q \<rightarrow>\<beta>\<bar>\<sigma> Ext P' x Q"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have "Ext P x Q \<rightarrow>\<beta> Ext M x Q" using M(1) by (rule EnvEps_Beta_Step.beta_step.ExtnL)
  moreover have "Ext M x Q \<rightarrow>\<sigma>\<^sup>* Ext P' x Q" using M(2) by (rule sigma_steps_ExtnL)
  moreover have "is_sigma_normal (Ext P' x Q)"
    using M(3) assms(2) by (rule is_sigma_normal.NF_Ext)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_ExtnR:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q"
  shows "Ext Q x P \<rightarrow>\<beta>\<bar>\<sigma> Ext Q x P'"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have "Ext Q x P \<rightarrow>\<beta> Ext Q x M" using M(1) by (rule EnvEps_Beta_Step.beta_step.ExtnR)
  moreover have "Ext Q x M \<rightarrow>\<sigma>\<^sup>* Ext Q x P'" using M(2) by (rule sigma_steps_ExtnR)
  moreover have "is_sigma_normal (Ext Q x P')"
    using assms(2) M(3) by (rule is_sigma_normal.NF_Ext)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

text \<open>Chain versions, by induction on the @{text "*"}-closure.\<close>

lemma beta_over_sigma_steps_Lam:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> Lam x P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Lam x P'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_Lam rtranclp.rtrancl_into_rtrancl)

lemma beta_over_sigma_steps_Eps:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> Eps P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Eps P'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_Eps rtranclp.rtrancl_into_rtrancl)

lemma beta_over_sigma_steps_AppL:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> is_sigma_normal Q \<Longrightarrow> App P Q \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App P' Q"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_AppL rtranclp.rtrancl_into_rtrancl)

lemma beta_over_sigma_steps_AppR:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> is_sigma_normal Q \<Longrightarrow> App Q P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App Q P'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_AppR rtranclp.rtrancl_into_rtrancl)

lemma beta_over_sigma_steps_ExtnL:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> is_sigma_normal Q \<Longrightarrow> Ext P x Q \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext P' x Q"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_ExtnL rtranclp.rtrancl_into_rtrancl)

lemma beta_over_sigma_steps_ExtnR:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> is_sigma_normal Q \<Longrightarrow> Ext Q x P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext Q x P'"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_ExtnR rtranclp.rtrancl_into_rtrancl)

text \<open>
  Lifting through @{text Comp} is not always safe (@{text Comp} can be a
  @{text "\<sigma>"}-redex), so the single-step lemmas below wrap the result in
  @{text sigma_nf} rather than requiring a side condition -- this makes
  them hold unconditionally, for @{text Comp} on either side, with no
  restriction on the shape of the fixed partner.
\<close>

lemma beta_over_sigma_step_CompL:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q"
  shows "Comp P Q \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp P' Q)"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have step1: "Comp P Q \<rightarrow>\<beta> Comp M Q" using M(1) by (rule EnvEps_Beta_Step.beta_step.CompL)
  have "Comp M Q \<rightarrow>\<sigma>\<^sup>* Comp P' Q" using M(2) by (rule sigma_steps_CompL)
  also have "Comp P' Q \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp P' Q)" by (rule sigma_nf_reduces)
  finally have step2: "Comp M Q \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp P' Q)" .
  have step3: "is_sigma_normal (sigma_nf (Comp P' Q))"
    using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)
  from step1 step2 step3 show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_CompR:
  assumes "V \<rightarrow>\<beta>\<bar>\<sigma> V'" and "is_sigma_normal P"
  shows "Comp P V \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp P V')"
proof -
  obtain M where M: "V \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* V'" "is_sigma_normal V'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have step1: "Comp P V \<rightarrow>\<beta> Comp P M" using M(1) by (rule EnvEps_Beta_Step.beta_step.CompR)
  have "Comp P M \<rightarrow>\<sigma>\<^sup>* Comp P V'" using M(2) by (rule sigma_steps_CompR)
  also have "Comp P V' \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp P V')" by (rule sigma_nf_reduces)
  finally have step2: "Comp P M \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp P V')" .
  have step3: "is_sigma_normal (sigma_nf (Comp P V'))"
    using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)
  from step1 step2 step3 show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_not_from_Id: "\<not> (Id \<rightarrow>\<beta>\<bar>\<sigma> X)"
  by (auto simp: beta_over_sigma_step_def elim: EnvEps_Beta_Step.beta_step.cases)

text \<open>
  Chain versions for a @{text Comp} whose fixed partner is @{text Lam}-
  or @{text Var}-headed: since @{text Id} has no outgoing
  @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}-step (the lemma above), any waypoint strictly before the
  end of a chain is @{text "\<noteq> Id"}, so @{text sigma_nf} is a no-op there
  and the single-step lemmas above chain together; only the very last
  step of the chain can trigger an @{text "Id"}-collapse.
\<close>

lemma beta_over_sigma_step_CompL_Lam:
  assumes "P \<rightarrow>\<beta>\<bar>\<sigma> P'" and "is_sigma_normal Q" and "Q \<noteq> Id"
  shows "Comp (Lam x P) Q \<rightarrow>\<beta>\<bar>\<sigma> Comp (Lam x P') Q"
proof -
  obtain M where M: "P \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* P'" "is_sigma_normal P'"
    using assms(1) by (auto simp: beta_over_sigma_step_def)
  have "Comp (Lam x P) Q \<rightarrow>\<beta> Comp (Lam x M) Q"
    using M(1) by (intro EnvEps_Beta_Step.beta_step.CompL EnvEps_Beta_Step.beta_step.Lam)
  moreover have "Comp (Lam x M) Q \<rightarrow>\<sigma>\<^sup>* Comp (Lam x P') Q"
    using M(2) by (intro sigma_steps_CompL sigma_steps_Lam)
  moreover have "is_sigma_normal (Comp (Lam x P') Q)"
    using M(3) assms(2,3) by (rule is_sigma_normal.NF_CompLam)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_steps_CompL_Lam:
  "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P' \<Longrightarrow> is_sigma_normal Q \<Longrightarrow> Q \<noteq> Id \<Longrightarrow> Comp (Lam x P) Q \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Comp (Lam x P') Q"
  by (induction rule: rtranclp.induct)
     (auto intro: beta_over_sigma_step_CompL_Lam rtranclp.rtrancl_into_rtrancl)

text \<open>
  Chain version of @{text CompR} for a @{text Lam}-headed fixed left
  partner: since @{text Id} has no outgoing @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}-step (the
  lemma above), any waypoint strictly before the end of the chain is
  @{text "\<noteq> Id"}, so @{text "Comp (Lam x U) _"} at that waypoint is
  already @{text "\<sigma>"}-normal (grammar's @{text NF_CompLam}) and
  @{text sigma_nf} is a no-op there; only the very last step of the
  chain can trigger an @{text Id}-collapse, which @{text
  beta_over_sigma_step_CompR} already accounts for.
\<close>

lemma beta_over_sigma_steps_CompR_Lam:
  assumes chain: "V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* V'" and nV: "is_sigma_normal V" and neV: "V \<noteq> Id"
    and nU: "is_sigma_normal U"
  shows "Comp (Lam x U) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Lam x U) V')"
  using chain
proof (induction rule: rtranclp_induct)
  case base
  have "is_sigma_normal (Comp (Lam x U) V)" by (intro is_sigma_normal.NF_CompLam nU nV neV)
  then have "sigma_irreducible (Comp (Lam x U) V)" by (simp add: sigma_normal_form_grammar)
  then have "sigma_nf (Comp (Lam x U) V) = Comp (Lam x U) V" by (rule sigma_nf_of_irreducible)
  then show ?case by simp
next
  case (step V1 V2)
  have nV1: "is_sigma_normal V1"
    using nV step.hyps(1) by (rule beta_over_sigma_steps_target_normal)
  have neV1: "V1 \<noteq> Id" using step.hyps(2) beta_over_sigma_step_not_from_Id by blast
  have nLamU: "is_sigma_normal (Lam x U)" using nU by (rule is_sigma_normal.NF_Lam)
  have "is_sigma_normal (Comp (Lam x U) V1)" by (intro is_sigma_normal.NF_CompLam nU nV1 neV1)
  then have "sigma_irreducible (Comp (Lam x U) V1)" by (simp add: sigma_normal_form_grammar)
  then have collapse: "sigma_nf (Comp (Lam x U) V1) = Comp (Lam x U) V1" by simp
  have "Comp (Lam x U) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Comp (Lam x U) V1"
    using step.IH unfolding collapse .
  also have "Comp (Lam x U) V1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Lam x U) V2)"
    using beta_over_sigma_step_CompR [OF step.hyps(2) nLamU]
    by (rule r_into_rtranclp)
  finally show ?case .
qed

text \<open>
  The two redex-firing single steps needed by
  @{text EnvEps_Parallel_Reduction_Soundness}'s @{text ParBeta} and
  @{text "ParComp\<^sub>\<epsilon>"} cases: after lifting both arguments to their
  targets via the lemmas above, one further @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}-step fires the
  redex itself and @{text "\<sigma>"}-normalizes the result.
\<close>

lemma beta_over_sigma_step_Beta:
  "App (Lam x U) V \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp U (Ext V x Id))"
proof -
  have "App (Lam x U) V \<rightarrow>\<beta> Comp U (Ext V x Id)" by (rule EnvEps_Beta_Step.beta_step.Beta)
  moreover have "Comp U (Ext V x Id) \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp U (Ext V x Id))" by (rule sigma_nf_reduces)
  moreover have "is_sigma_normal (sigma_nf (Comp U (Ext V x Id)))"
    using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_CompEps:
  "App (Eps U) V \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp U V)"
proof -
  have "App (Eps U) V \<rightarrow>\<beta> Comp U V" by (rule EnvEps_Beta_Step.beta_step.CompEps)
  moreover have "Comp U V \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp U V)" by (rule sigma_nf_reduces)
  moreover have "is_sigma_normal (sigma_nf (Comp U V))"
    using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

lemma beta_over_sigma_step_BetaClos:
  "App (Comp (Lam x U) L) V \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp U (Ext V x L))"
proof -
  have "App (Comp (Lam x U) L) V \<rightarrow>\<beta> Comp U (Ext V x L)"
    by (rule EnvEps_Beta_Step.beta_step.BetaClos)
  moreover have "Comp U (Ext V x L) \<rightarrow>\<sigma>\<^sup>* sigma_nf (Comp U (Ext V x L))"
    by (rule sigma_nf_reduces)
  moreover have "is_sigma_normal (sigma_nf (Comp U (Ext V x L)))"
    using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)
  ultimately show ?thesis by (auto simp: beta_over_sigma_step_def)
qed

end
