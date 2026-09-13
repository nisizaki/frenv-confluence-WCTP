theory EnvEps_Sigma_Root_Peaks
  imports EnvEps_Sigma_Assoc_Peak EnvEps_Sigma_Inner_Peaks
begin

text \<open>
  One lemma per rule of @{text "\<rightarrow>\<sigma>"}, each joining every peak whose first
  step is that rule. Together they are exactly the case analysis of
  @{text EnvEps_Sigma_Local_Confluence.sigma_locally_confluent}, split
  out so that each can invert the competing second step with the source
  kept as a variable (the @{text "X = \<dots>"} idiom used throughout this
  development, which keeps every rule parameter free under
  @{text sigma_step.induct}).

  The eight base-rule lemmas come first; the eight congruence-rule
  lemmas follow, each taking the joinability of the inner reducts as an
  explicit hypothesis @{text IH}, which the main theorem discharges from
  its induction hypothesis.
\<close>

subsection \<open>Base rules at the root\<close>

lemma assoc_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (Comp A B) C"
  shows "\<exists>L. Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: A B C rule: sigma_step.induct)
  case (Assoc P Q R)
  then have eq: "A = P" "B = Q" "C = R" by auto
  show ?case unfolding eq by blast
next
  case (IdR P)
  then have eq: "P = Comp A B" "C = Id" by auto
  have "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp A B"
    unfolding eq(2)
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) [symmetric] by blast
next
  case (CompL P P' Q)
  note step = CompL.hyps(1)
  from CompL have eq: "P = Comp A B" "Q = C" by auto
  from step have "Comp A B \<rightarrow>\<sigma> P'" unfolding eq(1) [symmetric] .
  from assoc_peak_join [OF this refl, of C]
  show ?case unfolding eq(2) [symmetric] by blast
next
  case (CompR Q Q' P)
  note step = CompR.hyps(1)
  from CompR have eq: "P = Comp A B" "Q = C" by auto
  have l: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp A (Comp B Q')"
    unfolding eq(2) [symmetric]
    by (rule sigma_step_into_steps
             [OF sigma_step.CompR [OF sigma_step.CompR [OF step]]])
  have r: "Comp P Q' \<rightarrow>\<sigma>\<^sup>* Comp A (Comp B Q')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  from l r show ?case by blast
qed simp_all

lemma idL_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp Id A"
  shows "\<exists>L. A \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: A rule: sigma_step.induct)
  case (IdL P)
  then have "A = P" by auto
  then show ?case by blast
next
  case (IdR P)
  then have eq: "P = Id" "A = Id" by auto
  show ?case unfolding eq by blast
next
  case (CompR Q Q' P)
  note step = CompR.hyps(1)
  from CompR have eq: "P = Id" "Q = A" by auto
  have l: "A \<rightarrow>\<sigma>\<^sup>* Q'"
    unfolding eq(2) [symmetric] by (rule sigma_step_into_steps [OF step])
  have r: "Comp P Q' \<rightarrow>\<sigma>\<^sup>* Q'"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.IdL])
  from l r show ?case by blast
qed simp_all

lemma idR_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp A Id"
  shows "\<exists>L. A \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: A rule: sigma_step.induct)
  case (Assoc P Q R)
  then have eq: "A = Comp P Q" "R = Id" by auto
  have "Comp P (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Comp P Q"
    unfolding eq(2)
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) by blast
next
  case (IdL P)
  then have eq: "A = Id" "P = Id" by auto
  show ?case unfolding eq by blast
next
  case (IdR P)
  then have "A = P" by auto
  then show ?case by blast
next
  case (DExtn L1 z M1 N1)
  \<comment> \<open>(2.25) @{text DExtn} / @{text IdR}.\<close>
  then have eq: "A = Ext L1 z M1" "N1 = Id" by auto
  have "Ext (Comp L1 N1) z (Comp M1 N1) \<rightarrow>\<sigma>\<^sup>* Ext L1 z M1"
    unfolding eq(2)
    by (rule sigma_2 [OF sigma_step.ExtnL [OF sigma_step.IdR]
                         sigma_step.ExtnR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) by blast
next
  case (DApp P Q R)
  \<comment> \<open>(2.29) @{text DApp} / @{text IdR}.\<close>
  then have eq: "A = App P Q" "R = Id" by auto
  have "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App P Q"
    unfolding eq(2)
    by (rule sigma_2 [OF sigma_step.AppL [OF sigma_step.IdR]
                         sigma_step.AppR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) by blast
next
  case (EpsEps P R)
  \<comment> \<open>(2.31) @{text EpsEps} / @{text IdR}.\<close>
  then have eq: "A = Eps P" "R = Id" by auto
  show ?case unfolding eq(1) by blast
next
  case (CompL P P' Q)
  note step = CompL.hyps(1)
  from CompL have eq: "P = A" "Q = Id" by auto
  have l: "A \<rightarrow>\<sigma>\<^sup>* P'"
    unfolding eq(1) [symmetric] by (rule sigma_step_into_steps [OF step])
  have r: "Comp P' Q \<rightarrow>\<sigma>\<^sup>* P'"
    unfolding eq(2) by (rule sigma_step_into_steps [OF sigma_step.IdR])
  from l r show ?case by blast
qed simp_all

lemma dExtn_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (Ext P z Q) R"
  shows "\<exists>L. Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P z Q R rule: sigma_step.induct)
  case (IdR P')
  \<comment> \<open>(2.25) again, reached from the other side.\<close>
  then have eq: "P' = Ext P z Q" "R = Id" by auto
  have "Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Ext P z Q"
    unfolding eq(2)
    by (rule sigma_2 [OF sigma_step.ExtnL [OF sigma_step.IdR]
                         sigma_step.ExtnR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) by blast
next
  case (DExtn L1 z1 M1 N1)
  then have eq: "P = L1" "z = z1" "Q = M1" "R = N1" by auto
  show ?case unfolding eq by blast
next
  case (CompL A A' B)
  note step = CompL.hyps(1)
  from CompL have eq: "A = Ext P z Q" "B = R" by auto
  from step have "Ext P z Q \<rightarrow>\<sigma> A'" unfolding eq(1) [symmetric] .
  from ext_inner_peak [OF this refl, of R]
  show ?case unfolding eq(2) [symmetric] by blast
next
  case (CompR B B' A)
  note step = CompR.hyps(1)
  from CompR have eq: "A = Ext P z Q" "B = R" by auto
  have l: "Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Ext (Comp P B') z (Comp Q B')"
    unfolding eq(2) [symmetric]
    by (rule sigma_2 [OF sigma_step.ExtnL [OF sigma_step.CompR [OF step]]
                         sigma_step.ExtnR [OF sigma_step.CompR [OF step]]])
  have r: "Comp A B' \<rightarrow>\<sigma>\<^sup>* Ext (Comp P B') z (Comp Q B')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.DExtn])
  from l r show ?case by blast
qed simp_all

lemma varRef_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (Var z) (Ext P z Q)"
  shows "\<exists>L. P \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: z P Q rule: sigma_step.induct)
  case (VarRef z1 P1 Q1)
  then have eq: "z = z1" "P = P1" "Q = Q1" by auto
  show ?case unfolding eq by blast
next
  case (CompR B B' A)
  note step = CompR.hyps(1)
  from CompR have eq: "A = Var z" "B = Ext P z Q" by auto
  from step have "Ext P z Q \<rightarrow>\<sigma> B'" unfolding eq(2) [symmetric] .
  from var_ref_inner_peak [OF this refl]
  show ?case unfolding eq(1) by blast
qed simp_all

lemma varSkip_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (Var z) (Ext P w Q)" and "z \<noteq> w"
  shows "\<exists>L. Comp (Var z) Q \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: z P w Q rule: sigma_step.induct)
  case (VarSkip z1 w1 P1 Q1)
  then have eq: "z = z1" "P = P1" "w = w1" "Q = Q1" by auto
  show ?case unfolding eq by blast
next
  case (CompR B B' A)
  note step = CompR.hyps(1)
  from CompR have eq: "A = Var z" "B = Ext P w Q" and neq: "z \<noteq> w" by auto
  from step have "Ext P w Q \<rightarrow>\<sigma> B'" unfolding eq(2) [symmetric] .
  from var_skip_inner_peak [OF this refl neq]
  show ?case unfolding eq(1) by blast
qed simp_all

lemma dApp_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (App P Q) R"
  shows "\<exists>L. App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P Q R rule: sigma_step.induct)
  case (IdR P')
  \<comment> \<open>(2.29) again, reached from the other side.\<close>
  then have eq: "P' = App P Q" "R = Id" by auto
  have "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App P Q"
    unfolding eq(2)
    by (rule sigma_2 [OF sigma_step.AppL [OF sigma_step.IdR]
                         sigma_step.AppR [OF sigma_step.IdR]])
  then show ?case unfolding eq(1) by blast
next
  case (DApp P1 Q1 R1)
  then have eq: "P = P1" "Q = Q1" "R = R1" by auto
  show ?case unfolding eq by blast
next
  case (CompL A A' B)
  note step = CompL.hyps(1)
  from CompL have eq: "A = App P Q" "B = R" by auto
  from step have "App P Q \<rightarrow>\<sigma> A'" unfolding eq(1) [symmetric] .
  from app_inner_peak [OF this refl, of R]
  show ?case unfolding eq(2) [symmetric] by blast
next
  case (CompR B B' A)
  note step = CompR.hyps(1)
  from CompR have eq: "A = App P Q" "B = R" by auto
  have l: "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App (Comp P B') (Comp Q B')"
    unfolding eq(2) [symmetric]
    by (rule sigma_2 [OF sigma_step.AppL [OF sigma_step.CompR [OF step]]
                         sigma_step.AppR [OF sigma_step.CompR [OF step]]])
  have r: "Comp A B' \<rightarrow>\<sigma>\<^sup>* App (Comp P B') (Comp Q B')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.DApp])
  from l r show ?case by blast
qed simp_all

lemma epsEps_root_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp (Eps P) R"
  shows "\<exists>L. Eps P \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P R rule: sigma_step.induct)
  case (IdR P')
  \<comment> \<open>(2.31) again, reached from the other side.\<close>
  then have eq: "P' = Eps P" "R = Id" by auto
  show ?case unfolding eq(1) by blast
next
  case (EpsEps P1 R1)
  then have eq: "P = P1" "R = R1" by auto
  show ?case unfolding eq by blast
next
  case (CompL A A' B)
  note step = CompL.hyps(1)
  from CompL have eq: "A = Eps P" "B = R" by auto
  from step have "Eps P \<rightarrow>\<sigma> A'" unfolding eq(1) [symmetric] .
  from eps_inner_peak [OF this refl, of R]
  show ?case unfolding eq(2) [symmetric] by blast
next
  case (CompR B B' A)
  note step = CompR.hyps(1)
  from CompR have eq: "A = Eps P" "B = R" by auto
  have r: "Comp A B' \<rightarrow>\<sigma>\<^sup>* Eps P"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.EpsEps])
  from r show ?case by blast
qed simp_all

subsection \<open>Congruence rules at the root\<close>

lemma appL_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = App M N" and "M \<rightarrow>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. App M' N \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (AppL A A' B)
  note step = AppL.hyps(1)
  from AppL have eq: "M = A" "N = B" by auto
  from step have "M \<rightarrow>\<sigma> A'" unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "App M' N \<rightarrow>\<sigma>\<^sup>* App L0 N" using L0(1) by (rule sigma_steps_AppL)
  moreover have "App A' B \<rightarrow>\<sigma>\<^sup>* App L0 N"
    unfolding eq(2) [symmetric] using L0(2) by (rule sigma_steps_AppL)
  ultimately show ?case by blast
next
  case (AppR B B' A)
  note step2 = AppR.hyps(1)
  from AppR have eq: "M = A" "N = B" by auto
  from step2 have stepN: "N \<rightarrow>\<sigma> B'" unfolding eq(2) .
  have l: "App M' N \<rightarrow>\<sigma>\<^sup>* App M' B'"
    by (rule sigma_step_into_steps [OF sigma_step.AppR [OF stepN]])
  have r: "App A B' \<rightarrow>\<sigma>\<^sup>* App M' B'"
    unfolding eq(1) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.AppL [OF assms(3)]])
  from l r show ?case by blast
qed simp_all

lemma appR_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = App M N" and "N \<rightarrow>\<sigma> N'"
    and IH: "\<And>W. N \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. N' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. App M N' \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (AppL A A' B)
  note step = AppL.hyps(1)
  from AppL have eq: "M = A" "N = B" by auto
  have l: "App M N' \<rightarrow>\<sigma>\<^sup>* App A' N'"
    unfolding eq(1)
    by (rule sigma_step_into_steps [OF sigma_step.AppL [OF step]])
  have r: "App A' B \<rightarrow>\<sigma>\<^sup>* App A' N'"
    unfolding eq(2) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.AppR [OF assms(3)]])
  from l r show ?case by blast
next
  case (AppR B B' A)
  note step = AppR.hyps(1)
  from AppR have eq: "M = A" "N = B" by auto
  from step have "N \<rightarrow>\<sigma> B'" unfolding eq(2) .
  from IH [OF this] obtain L0 where L0: "N' \<rightarrow>\<sigma>\<^sup>* L0" "B' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "App M N' \<rightarrow>\<sigma>\<^sup>* App M L0" using L0(1) by (rule sigma_steps_AppR)
  moreover have "App A B' \<rightarrow>\<sigma>\<^sup>* App M L0"
    unfolding eq(1) [symmetric] using L0(2) by (rule sigma_steps_AppR)
  ultimately show ?case by blast
qed simp_all

lemma lam_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Lam x M" and "M \<rightarrow>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Lam x M' \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (Lam A A' y)
  note step = Lam.hyps(1)
  from Lam have eq: "M = A" "x = y" by auto
  from step have "M \<rightarrow>\<sigma> A'" unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Lam x M' \<rightarrow>\<sigma>\<^sup>* Lam x L0" using L0(1) by (rule sigma_steps_Lam)
  moreover have "Lam y A' \<rightarrow>\<sigma>\<^sup>* Lam x L0"
    unfolding eq(2) [symmetric] using L0(2) by (rule sigma_steps_Lam)
  ultimately show ?case by blast
qed simp_all

lemma eop_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Eps M" and "M \<rightarrow>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Eps M' \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (Eop A A')
  note step = Eop.hyps(1)
  from Eop have eq: "M = A" by auto
  from step have "M \<rightarrow>\<sigma> A'" unfolding eq .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Eps M' \<rightarrow>\<sigma>\<^sup>* Eps L0" using L0(1) by (rule sigma_steps_Eop)
  moreover have "Eps A' \<rightarrow>\<sigma>\<^sup>* Eps L0" using L0(2) by (rule sigma_steps_Eop)
  ultimately show ?case by blast
qed simp_all

lemma extnL_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Ext M x N" and "M \<rightarrow>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Ext M' x N \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (ExtnL A A' y B)
  note step = ExtnL.hyps(1)
  from ExtnL have eq: "M = A" "x = y" "N = B" by auto
  from step have "M \<rightarrow>\<sigma> A'" unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Ext M' x N \<rightarrow>\<sigma>\<^sup>* Ext L0 x N" using L0(1) by (rule sigma_steps_ExtnL)
  moreover have "Ext A' y B \<rightarrow>\<sigma>\<^sup>* Ext L0 x N"
    unfolding eq(2) [symmetric] eq(3) [symmetric]
    using L0(2) by (rule sigma_steps_ExtnL)
  ultimately show ?case by blast
next
  case (ExtnR B B' A y)
  note step2 = ExtnR.hyps(1)
  from ExtnR have eq: "M = A" "x = y" "N = B" by auto
  from step2 have stepN: "N \<rightarrow>\<sigma> B'" unfolding eq(3) .
  have l: "Ext M' x N \<rightarrow>\<sigma>\<^sup>* Ext M' x B'"
    by (rule sigma_step_into_steps [OF sigma_step.ExtnR [OF stepN]])
  have r: "Ext A y B' \<rightarrow>\<sigma>\<^sup>* Ext M' x B'"
    unfolding eq(1) [symmetric] eq(2) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.ExtnL [OF assms(3)]])
  from l r show ?case by blast
qed simp_all

lemma extnR_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Ext M x N" and "N \<rightarrow>\<sigma> N'"
    and IH: "\<And>W. N \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. N' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Ext M x N' \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (ExtnL A A' y B)
  note step = ExtnL.hyps(1)
  from ExtnL have eq: "M = A" "x = y" "N = B" by auto
  have l: "Ext M x N' \<rightarrow>\<sigma>\<^sup>* Ext A' x N'"
    unfolding eq(1)
    by (rule sigma_step_into_steps [OF sigma_step.ExtnL [OF step]])
  have r: "Ext A' y B \<rightarrow>\<sigma>\<^sup>* Ext A' x N'"
    unfolding eq(2) [symmetric] eq(3) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.ExtnR [OF assms(3)]])
  from l r show ?case by blast
next
  case (ExtnR B B' A y)
  note step = ExtnR.hyps(1)
  from ExtnR have eq: "M = A" "x = y" "N = B" by auto
  from step have "N \<rightarrow>\<sigma> B'" unfolding eq(3) .
  from IH [OF this] obtain L0 where L0: "N' \<rightarrow>\<sigma>\<^sup>* L0" "B' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Ext M x N' \<rightarrow>\<sigma>\<^sup>* Ext M x L0" using L0(1) by (rule sigma_steps_ExtnR)
  moreover have "Ext A y B' \<rightarrow>\<sigma>\<^sup>* Ext M x L0"
    unfolding eq(1) [symmetric] eq(2) [symmetric]
    using L0(2) by (rule sigma_steps_ExtnR)
  ultimately show ?case by blast
qed simp_all

lemma compL_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp M N" and step: "M \<rightarrow>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Comp M' N \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (Assoc P Q R)
  then have eq: "M = Comp P Q" "N = R" by auto
  from step have "Comp P Q \<rightarrow>\<sigma> M'" unfolding eq(1) [symmetric] .
  from assoc_peak_join [OF this refl, of R]
  show ?case unfolding eq(2) by blast
next
  case (IdR P)
  then have eq: "P = M" "N = Id" by auto
  have l: "Comp M' N \<rightarrow>\<sigma>\<^sup>* M'"
    unfolding eq(2) by (rule sigma_step_into_steps [OF sigma_step.IdR])
  have r: "P \<rightarrow>\<sigma>\<^sup>* M'"
    unfolding eq(1) by (rule sigma_step_into_steps [OF step])
  from l r show ?case by blast
next
  case (DExtn L1 z M1 N1)
  then have eq: "M = Ext L1 z M1" "N = N1" by auto
  from step have "Ext L1 z M1 \<rightarrow>\<sigma> M'" unfolding eq(1) [symmetric] .
  from ext_inner_peak [OF this refl, of N1]
  show ?case unfolding eq(2) by blast
next
  case (DApp P Q R)
  then have eq: "M = App P Q" "N = R" by auto
  from step have "App P Q \<rightarrow>\<sigma> M'" unfolding eq(1) [symmetric] .
  from app_inner_peak [OF this refl, of R]
  show ?case unfolding eq(2) by blast
next
  case (EpsEps P R)
  then have eq: "M = Eps P" "N = R" by auto
  from step have "Eps P \<rightarrow>\<sigma> M'" unfolding eq(1) [symmetric] .
  from eps_inner_peak [OF this refl, of R]
  show ?case unfolding eq(2) by blast
next
  case (CompL A A' B)
  note step2 = CompL.hyps(1)
  from CompL have eq: "M = A" "N = B" by auto
  from step2 have "M \<rightarrow>\<sigma> A'" unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Comp M' N \<rightarrow>\<sigma>\<^sup>* Comp L0 N" using L0(1) by (rule sigma_steps_CompL)
  moreover have "Comp A' B \<rightarrow>\<sigma>\<^sup>* Comp L0 N"
    unfolding eq(2) [symmetric] using L0(2) by (rule sigma_steps_CompL)
  ultimately show ?case by blast
next
  case (CompR B B' A)
  note step2 = CompR.hyps(1)
  from CompR have eq: "M = A" "N = B" by auto
  from step2 have stepN: "N \<rightarrow>\<sigma> B'" unfolding eq(2) .
  have l: "Comp M' N \<rightarrow>\<sigma>\<^sup>* Comp M' B'"
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF stepN]])
  have r: "Comp A B' \<rightarrow>\<sigma>\<^sup>* Comp M' B'"
    unfolding eq(1) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.CompL [OF step]])
  from l r show ?case by blast
next
  case (IdL P)
  \<comment> \<open>@{term M} would have to be @{term Id}, which takes no step.\<close>
  then have "M = Id" by auto
  with step show ?case by simp
next
  case (VarRef z P Q)
  \<comment> \<open>@{term M} would have to be a variable, which takes no step.\<close>
  then have "M = Var z" by auto
  with step show ?case by simp
next
  case (VarSkip z w P Q)
  \<comment> \<open>Likewise @{term M} would have to be a variable.\<close>
  then have "M = Var z" by auto
  with step show ?case by simp
qed simp_all

lemma compR_peak:
  assumes "X \<rightarrow>\<sigma> N\<^sub>2" and "X = Comp M N" and step: "N \<rightarrow>\<sigma> N'"
    and IH: "\<And>W. N \<rightarrow>\<sigma> W \<Longrightarrow> \<exists>L. N' \<rightarrow>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<sigma>\<^sup>* L"
  shows "\<exists>L. Comp M N' \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: sigma_step.induct)
  case (Assoc P Q R)
  then have eq: "M = Comp P Q" "N = R" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q N')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  have r: "Comp P (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q N')"
    unfolding eq(2) [symmetric]
    by (rule sigma_step_into_steps
             [OF sigma_step.CompR [OF sigma_step.CompR [OF step]]])
  from l r show ?case by blast
next
  case (IdL P)
  then have eq: "M = Id" "P = N" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* N'"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.IdL])
  have r: "P \<rightarrow>\<sigma>\<^sup>* N'"
    unfolding eq(2) by (rule sigma_step_into_steps [OF step])
  from l r show ?case by blast
next
  case (DExtn L1 z M1 N1)
  then have eq: "M = Ext L1 z M1" "N = N1" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* Ext (Comp L1 N') z (Comp M1 N')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.DExtn])
  have r: "Ext (Comp L1 N1) z (Comp M1 N1)
             \<rightarrow>\<sigma>\<^sup>* Ext (Comp L1 N') z (Comp M1 N')"
    unfolding eq(2) [symmetric]
    by (rule sigma_2 [OF sigma_step.ExtnL [OF sigma_step.CompR [OF step]]
                         sigma_step.ExtnR [OF sigma_step.CompR [OF step]]])
  from l r show ?case by blast
next
  case (VarRef z P Q)
  then have eq: "M = Var z" "N = Ext P z Q" by auto
  from step have "Ext P z Q \<rightarrow>\<sigma> N'" unfolding eq(2) [symmetric] .
  from var_ref_inner_peak [OF this refl]
  show ?case unfolding eq(1) by blast
next
  case (VarSkip z w P Q)
  then have eq: "M = Var z" "N = Ext P w Q" and neq: "z \<noteq> w" by auto
  from step have "Ext P w Q \<rightarrow>\<sigma> N'" unfolding eq(2) [symmetric] .
  from var_skip_inner_peak [OF this refl neq]
  show ?case unfolding eq(1) by blast
next
  case (DApp P Q R)
  then have eq: "M = App P Q" "N = R" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* App (Comp P N') (Comp Q N')"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.DApp])
  have r: "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App (Comp P N') (Comp Q N')"
    unfolding eq(2) [symmetric]
    by (rule sigma_2 [OF sigma_step.AppL [OF sigma_step.CompR [OF step]]
                         sigma_step.AppR [OF sigma_step.CompR [OF step]]])
  from l r show ?case by blast
next
  case (EpsEps P R)
  then have eq: "M = Eps P" "N = R" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* Eps P"
    unfolding eq(1) by (rule sigma_step_into_steps [OF sigma_step.EpsEps])
  from l show ?case by blast
next
  case (CompL A A' B)
  note step2 = CompL.hyps(1)
  from CompL have eq: "M = A" "N = B" by auto
  have l: "Comp M N' \<rightarrow>\<sigma>\<^sup>* Comp A' N'"
    unfolding eq(1)
    by (rule sigma_step_into_steps [OF sigma_step.CompL [OF step2]])
  have r: "Comp A' B \<rightarrow>\<sigma>\<^sup>* Comp A' N'"
    unfolding eq(2) [symmetric]
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF step]])
  from l r show ?case by blast
next
  case (CompR B B' A)
  note step2 = CompR.hyps(1)
  from CompR have eq: "M = A" "N = B" by auto
  from step2 have "N \<rightarrow>\<sigma> B'" unfolding eq(2) .
  from IH [OF this] obtain L0 where L0: "N' \<rightarrow>\<sigma>\<^sup>* L0" "B' \<rightarrow>\<sigma>\<^sup>* L0" by blast
  have "Comp M N' \<rightarrow>\<sigma>\<^sup>* Comp M L0" using L0(1) by (rule sigma_steps_CompR)
  moreover have "Comp A B' \<rightarrow>\<sigma>\<^sup>* Comp M L0"
    unfolding eq(1) [symmetric] using L0(2) by (rule sigma_steps_CompR)
  ultimately show ?case by blast
next
  case (IdR P)
  \<comment> \<open>@{term N} would have to be @{term Id}, which takes no step.\<close>
  then have "N = Id" by auto
  with step show ?case by simp
qed simp_all

end
