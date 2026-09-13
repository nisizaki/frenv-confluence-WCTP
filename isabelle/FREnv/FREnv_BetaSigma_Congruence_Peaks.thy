theory FREnv_BetaSigma_Congruence_Peaks
  imports FREnv_BetaSigma_Root_Peaks
begin

text \<open>
  One lemma per congruence rule of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} (roadmap item 4),
  mirroring @{text "EnvEps.EnvEps_Sigma_Root_Peaks"}'s "Congruence rules
  at the root" section. Each takes the joinability of the inner reducts
  as an explicit hypothesis @{text IH}, discharged by the main theorem's
  own induction hypothesis.

  Unlike @{text "lambda_EnvEps"}'s @{text "\<rightarrow>\<sigma>"} (roadmap item 11, no
  @{text Beta}/@{text BetaClos}), @{text "App M N"} is not a "safe"
  congruence position here: since every base rule's own left-hand side
  is @{text App}-headed, @{text M} (or @{text "App M N"} once @{text M}
  is @{text Eps}-headed) can itself already be shaped like any of the
  ten base rules' own redex, giving @{text appL_peak}/@{text appR_peak}
  the same breadth as @{text FREnv_BetaSigma_DApp_Peak.frenv_dapp_peak_join}.
  @{text Lam}, @{text Ext}, and @{text Eps} are still safe (no base rule
  has a @{text Lam}-, @{text Ext}-, or bare @{text Eps}-headed left-hand
  side), so @{text lam_peak}/@{text extnL_peak}/@{text extnR_peak}/
  @{text envAbst_peak} stay as simple as their @{text "lambda_EnvEps"}
  counterparts.
\<close>

lemma appL_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App M N" and "M \<rightarrow>\<beta>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (Beta x M1 N1)
  then have eq: "M = Lam x M1" "N = N1" by auto
  have "Lam x M1 \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain M1' where M'eq: "M' = Lam x M1'" and stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1') (Ext N1 x Id)"
    unfolding M'eq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
  have r: "App (Eps M1) (Ext N1 x Id) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1') (Ext N1 x Id)"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM1]]])
  from l r show ?case by blast
next
  case (BetaClos x M1 L1 N1)
  then have eq: "M = App (Eps (Lam x M1)) L1" "N = N1" by auto
  have step1: "App (Eps (Lam x M1)) L1 \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  from step1 show ?case
  proof (cases rule: beta_sigma_step.cases)
    case IdR
    then have L1eq: "L1 = Id" and M'eq: "M' = Lam x M1" by auto
    have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N1 x Id)"
      unfolding M'eq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
    from l show ?thesis unfolding L1eq using rtranclp.rtrancl_refl by blast
  next
    case (AppL P0')
    then have step2: "Eps (Lam x M1) \<rightarrow>\<beta>\<sigma> P0'" and M'eq: "M' = App P0' L1" by auto
    from step2 obtain W where P0'eq: "P0' = Eps W" and stepLxM1: "Lam x M1 \<rightarrow>\<beta>\<sigma> W"
      by (cases rule: beta_sigma_step.cases) auto
    from stepLxM1 obtain M1' where Weq: "W = Lam x M1'" and stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'"
      by (cases rule: beta_sigma_step.cases) auto
    have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1') (Ext N1 x L1)"
      unfolding M'eq P0'eq Weq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
    have r: "App (Eps M1) (Ext N1 x L1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1') (Ext N1 x L1)"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM1]]])
    from l r show ?thesis by blast
  next
    case (AppR L1')
    then have stepL1: "L1 \<rightarrow>\<beta>\<sigma> L1'" and M'eq: "M' = App (Eps (Lam x M1)) L1'" by auto
    have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N1 x L1')"
      unfolding M'eq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
    have r: "App (Eps M1) (Ext N1 x L1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N1 x L1')"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnR [OF stepL1]]])
    from l r show ?thesis by blast
  qed
next
  case (Assoc L1 M1 N1)
  then have eq: "M = Eps (App (Eps L1) M1)" "N = N1" by auto
  have "Eps (App (Eps L1) M1) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain W where M'eq: "M' = Eps W" and stepW: "App (Eps L1) M1 \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from frenv_assoc_peak_join [OF stepW refl, of N1]
  obtain K where K1: "App (Eps W) N1 \<rightarrow>\<beta>\<sigma>\<^sup>* K" and K2: "App (Eps L1) (App (Eps M1) N1) \<rightarrow>\<beta>\<sigma>\<^sup>* K"
    by blast
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* K" unfolding M'eq eq(2) using K1 .
  from l K2 show ?case by blast
next
  case (IdL M1)
  then have eq: "M = Eps Id" by auto
  have "Eps Id \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq .
  then obtain Id' where "Id \<rightarrow>\<beta>\<sigma> Id'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_id_not_from_step show ?case by blast
next
  case (IdR M1)
  then have eq: "M = Eps M1" "N = Id" by auto
  have "Eps M1 \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain M1' where M'eq: "M' = Eps M1'" and stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* M1'"
    unfolding M'eq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.IdR])
  have r: "M1 \<rightarrow>\<beta>\<sigma>\<^sup>* M1'" by (rule bs_step_into_steps [OF stepM1])
  from l r show ?case by blast
next
  case (DExtn L1 x M1 N1)
  then have eq: "M = Eps (Ext L1 x M1)" "N = N1" by auto
  have "Eps (Ext L1 x M1) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain W where M'eq: "M' = Eps W" and stepEW: "Ext L1 x M1 \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from stepEW show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL L1')
    then have stepL1: "L1 \<rightarrow>\<beta>\<sigma> L1'" and Weq: "W = Ext L1' x M1" by auto
    have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1') N1) x (App (Eps M1) N1)"
      unfolding M'eq Weq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
    have r: "Ext (App (Eps L1) N1) x (App (Eps M1) N1)
               \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1') N1) x (App (Eps M1) N1)"
      by (rule bs_step_into_steps
            [OF beta_sigma_step.ExtnL [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepL1]]]])
    from l r show ?thesis by blast
  next
    case (ExtnR M1')
    then have stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'" and Weq: "W = Ext L1 x M1'" by auto
    have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) N1) x (App (Eps M1') N1)"
      unfolding M'eq Weq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
    have r: "Ext (App (Eps L1) N1) x (App (Eps M1) N1)
               \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) N1) x (App (Eps M1') N1)"
      by (rule bs_step_into_steps
            [OF beta_sigma_step.ExtnR [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM1]]]])
    from l r show ?thesis by blast
  qed
next
  case (VarRef x M1 N1)
  then have eq: "M = Eps (Var x)" by auto
  have "Eps (Var x) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq .
  then obtain V' where "Var x \<rightarrow>\<beta>\<sigma> V'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_var_not_from_step show ?case by blast
next
  case (VarSkip x y M1 N1)
  then have eq: "M = Eps (Var y)" by auto
  have "Eps (Var y) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq .
  then obtain V' where "Var y \<rightarrow>\<beta>\<sigma> V'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_var_not_from_step show ?case by blast
next
  case (DApp M1 N1 L1)
  then have eq: "M = Eps (App M1 N1)" "N = L1" by auto
  have "Eps (App M1 N1) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain W where M'eq: "M' = Eps W" and stepW: "App M1 N1 \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from frenv_dapp_peak_join [OF stepW refl, of L1]
  obtain K where K1: "App (Eps W) L1 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
      and K2: "App (App (Eps M1) L1) (App (Eps N1) L1) \<rightarrow>\<beta>\<sigma>\<^sup>* K" by blast
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* K" unfolding M'eq eq(2) using K1 .
  from l K2 show ?case by blast
next
  case (EpsEps M1 N1)
  then have eq: "M = Eps (Eps M1)" "N = N1" by auto
  have "Eps (Eps M1) \<rightarrow>\<beta>\<sigma> M'" using assms(3) unfolding eq(1) .
  then obtain W where M'eq: "M' = Eps W" and stepEM1: "Eps M1 \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from stepEM1 obtain M1' where Weq: "W = Eps M1'" and stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M1'"
    unfolding M'eq Weq eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  have r: "Eps M1 \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M1'"
    by (rule bs_step_into_steps [OF beta_sigma_step.EnvAbst [OF stepM1]])
  from l r show ?case by blast
next
  case (AppL A A' B)
  from AppL have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" "N = B" by auto
  have "M \<rightarrow>\<beta>\<sigma> A'" using step unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App L0 N" using L0(1) by (rule bs_steps_AppL)
  moreover have "App A' B \<rightarrow>\<beta>\<sigma>\<^sup>* App L0 N"
    unfolding eq(2) [symmetric] using L0(2) by (rule bs_steps_AppL)
  ultimately show ?case by blast
next
  case (AppR B B' A)
  from AppR have step: "B \<rightarrow>\<beta>\<sigma> B'" and eq: "M = A" "N = B" by auto
  have l: "App M' N \<rightarrow>\<beta>\<sigma>\<^sup>* App M' B'"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF step]])
  have r: "App A B' \<rightarrow>\<beta>\<sigma>\<^sup>* App M' B'"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF assms(3)]])
  from l r show ?case by blast
qed simp_all

lemma appR_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App M N" and "N \<rightarrow>\<beta>\<sigma> N'"
    and IH: "\<And>W. N \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. N' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (Beta x M1 N1)
  then have eq: "M = Lam x M1" "N = N1" by auto
  have stepN1: "N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N' x Id)"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
  have r: "App (Eps M1) (Ext N1 x Id) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N' x Id)"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnL [OF stepN1]]])
  from l r show ?case by blast
next
  case (BetaClos x M1 L1 N1)
  then have eq: "M = App (Eps (Lam x M1)) L1" "N = N1" by auto
  have stepN1: "N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N' x L1)"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
  have r: "App (Eps M1) (Ext N1 x L1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext N' x L1)"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnL [OF stepN1]]])
  from l r show ?case by blast
next
  case (Assoc L1 M1 N1)
  then have eq: "M = Eps (App (Eps L1) M1)" "N = N1" by auto
  have stepN1: "N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) N')"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  have r: "App (Eps L1) (App (Eps M1) N1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) N')"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.AppR [OF stepN1]]])
  from l r show ?case by blast
next
  case (IdL M1)
  then have eq: "M = Eps Id" "N = M1" by auto
  have step: "M1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* N'"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.IdL])
  have r: "M1 \<rightarrow>\<beta>\<sigma>\<^sup>* N'" by (rule bs_step_into_steps [OF step])
  from l r show ?case by blast
next
  case (IdR M1)
  then have eq: "N = Id" by auto
  have "Id \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq .
  with frenv_id_not_from_step show ?case by blast
next
  case (DExtn L1 x M1 N1)
  then have eq: "M = Eps (Ext L1 x M1)" "N = N1" by auto
  have stepN1: "N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) N') x (App (Eps M1) N')"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
  have r: "Ext (App (Eps L1) N1) x (App (Eps M1) N1)
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) N') x (App (Eps M1) N')"
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.AppR [OF stepN1]]]
              bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.AppR [OF stepN1]]]])
  from l r show ?case by blast
next
  case (VarRef x M1 N1)
  then have eq: "M = Eps (Var x)" "N = Ext M1 x N1" by auto
  have "Ext M1 x N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  then show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL M1')
    then have stepM1: "M1 \<rightarrow>\<beta>\<sigma> M1'" and N'eq: "N' = Ext M1' x N1" by auto
    have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* M1'"
      unfolding N'eq eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.VarRef])
    have r: "M1 \<rightarrow>\<beta>\<sigma>\<^sup>* M1'" by (rule bs_step_into_steps [OF stepM1])
    from l r show ?thesis by blast
  next
    case (ExtnR N1')
    then have N'eq: "N' = Ext M1 x N1'" by auto
    have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* M1"
      unfolding N'eq eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.VarRef])
    from l show ?thesis using rtranclp.rtrancl_refl by blast
  qed
next
  case (VarSkip x y M1 N1)
  then have eq: "M = Eps (Var y)" "N = Ext M1 x N1" and neq: "x \<noteq> y" by auto
  have "Ext M1 x N1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  then show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL M1')
    then have N'eq: "N' = Ext M1' x N1" by auto
    have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N1"
      unfolding N'eq eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]])
    from l show ?thesis using rtranclp.rtrancl_refl by blast
  next
    case (ExtnR N1')
    then have stepN1: "N1 \<rightarrow>\<beta>\<sigma> N1'" and N'eq: "N' = Ext M1 x N1'" by auto
    have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N1'"
      unfolding N'eq eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]])
    have r: "App (Eps (Var y)) N1 \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N1'"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF stepN1]])
    from l r show ?thesis by blast
  qed
next
  case (DApp M1 N1 L1)
  then have eq: "M = Eps (App M1 N1)" "N = L1" by auto
  have stepL1: "L1 \<rightarrow>\<beta>\<sigma> N'" using assms(3) unfolding eq(2) .
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M1) N') (App (Eps N1) N')"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.DApp])
  have r: "App (App (Eps M1) L1) (App (Eps N1) L1)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M1) N') (App (Eps N1) N')"
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.AppR [OF stepL1]]]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.AppR [OF stepL1]]]])
  from l r show ?case by blast
next
  case (EpsEps M1 N1)
  then have eq: "M = Eps (Eps M1)" "N = N1" by auto
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M1"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  from l show ?case using rtranclp.rtrancl_refl by blast
next
  case (AppL A A' B)
  from AppL have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" "N = B" by auto
  have l: "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App A' N'"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF step]])
  have r: "App A' B \<rightarrow>\<beta>\<sigma>\<^sup>* App A' N'"
    unfolding eq(2) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF assms(3)]])
  from l r show ?case by blast
next
  case (AppR B B' A)
  from AppR have step: "B \<rightarrow>\<beta>\<sigma> B'" and eq: "M = A" "N = B" by auto
  have "N \<rightarrow>\<beta>\<sigma> B'" using step unfolding eq(2) .
  from IH [OF this] obtain L0 where L0: "N' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "B' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "App M N' \<rightarrow>\<beta>\<sigma>\<^sup>* App M L0" using L0(1) by (rule bs_steps_AppR)
  moreover have "App A B' \<rightarrow>\<beta>\<sigma>\<^sup>* App M L0"
    unfolding eq(1) [symmetric] using L0(2) by (rule bs_steps_AppR)
  ultimately show ?case by blast
qed simp_all

lemma lam_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = Lam x M" and "M \<rightarrow>\<beta>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. Lam x M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (Lam A A' y)
  from Lam have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" "x = y" by auto
  have "M \<rightarrow>\<beta>\<sigma> A'" using step unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "Lam x M' \<rightarrow>\<beta>\<sigma>\<^sup>* Lam x L0" using L0(1) by (rule bs_steps_Lam)
  moreover have "Lam y A' \<rightarrow>\<beta>\<sigma>\<^sup>* Lam x L0"
    unfolding eq(2) [symmetric] using L0(2) by (rule bs_steps_Lam)
  ultimately show ?case by blast
qed simp_all

lemma extnL_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = Ext M x N" and "M \<rightarrow>\<beta>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. Ext M' x N \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (ExtnL A A' y B)
  from ExtnL have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" "x = y" "N = B" by auto
  have "M \<rightarrow>\<beta>\<sigma> A'" using step unfolding eq(1) .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "Ext M' x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext L0 x N" using L0(1) by (rule bs_steps_ExtnL)
  moreover have "Ext A' y B \<rightarrow>\<beta>\<sigma>\<^sup>* Ext L0 x N"
    unfolding eq(2) [symmetric] eq(3) [symmetric] using L0(2) by (rule bs_steps_ExtnL)
  ultimately show ?case by blast
next
  case (ExtnR B B' A y)
  from ExtnR have step2: "B \<rightarrow>\<beta>\<sigma> B'" and eq: "M = A" "x = y" "N = B" by auto
  have l: "Ext M' x N \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M' x B'"
    unfolding eq(3) by (rule bs_step_into_steps [OF beta_sigma_step.ExtnR [OF step2]])
  have r: "Ext A y B' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M' x B'"
    unfolding eq(1) [symmetric] eq(2) [symmetric]
    by (rule bs_step_into_steps [OF beta_sigma_step.ExtnL [OF assms(3)]])
  from l r show ?case by blast
qed simp_all

lemma extnR_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = Ext M x N" and "N \<rightarrow>\<beta>\<sigma> N'"
    and IH: "\<And>W. N \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. N' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. Ext M x N' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (ExtnL A A' y B)
  from ExtnL have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" "x = y" "N = B" by auto
  have l: "Ext M x N' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext A' x N'"
    unfolding eq(1) by (rule bs_step_into_steps [OF beta_sigma_step.ExtnL [OF step]])
  have r: "Ext A' y B \<rightarrow>\<beta>\<sigma>\<^sup>* Ext A' x N'"
    unfolding eq(2) [symmetric] eq(3) [symmetric]
    by (rule bs_step_into_steps [OF beta_sigma_step.ExtnR [OF assms(3)]])
  from l r show ?case by blast
next
  case (ExtnR B B' A y)
  from ExtnR have step2: "B \<rightarrow>\<beta>\<sigma> B'" and eq: "M = A" "x = y" "N = B" by auto
  have "N \<rightarrow>\<beta>\<sigma> B'" using step2 unfolding eq(3) .
  from IH [OF this] obtain L0 where L0: "N' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "B' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "Ext M x N' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M x L0" using L0(1) by (rule bs_steps_ExtnR)
  moreover have "Ext A y B' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext M x L0"
    unfolding eq(1) [symmetric] eq(2) [symmetric] using L0(2) by (rule bs_steps_ExtnR)
  ultimately show ?case by blast
qed simp_all

lemma envAbst_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = Eps M" and "M \<rightarrow>\<beta>\<sigma> M'"
    and IH: "\<And>W. M \<rightarrow>\<beta>\<sigma> W \<Longrightarrow> \<exists>L. M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> W \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  shows "\<exists>L. Eps M' \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms(1,2)
proof (induction rule: beta_sigma_step.induct)
  case (EnvAbst A A')
  from EnvAbst have step: "A \<rightarrow>\<beta>\<sigma> A'" and eq: "M = A" by auto
  have "M \<rightarrow>\<beta>\<sigma> A'" using step unfolding eq .
  from IH [OF this] obtain L0 where L0: "M' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" "A' \<rightarrow>\<beta>\<sigma>\<^sup>* L0" by blast
  have "Eps M' \<rightarrow>\<beta>\<sigma>\<^sup>* Eps L0" using L0(1) by (rule bs_steps_EnvAbst)
  moreover have "Eps A' \<rightarrow>\<beta>\<sigma>\<^sup>* Eps L0" using L0(2) by (rule bs_steps_EnvAbst)
  ultimately show ?case by blast
qed simp_all

end
