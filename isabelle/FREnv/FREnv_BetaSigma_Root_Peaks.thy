theory FREnv_BetaSigma_Root_Peaks
  imports FREnv_BetaSigma_Assoc_Peak FREnv_BetaSigma_DApp_Peak
begin

text \<open>
  One lemma per base rule of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"}, each joining every peak whose
  first step is that rule (docs file
  @{text "docs/frenv-beta-sigma-local-confluence.md"}, \<section>3.1's
  same-root overlaps @{text R1}-@{text R6}/@{text C1}, plus the
  structural congruence cases; roadmap item 4). Mirroring
  @{text "EnvEps.EnvEps_Sigma_Root_Peaks"}, the source is kept as a
  variable @{text X} with an explicit shape equation so that @{text
  "beta_sigma_step.induct"} leaves every rule's own parameters free.

  The @{text Beta}/@{text BetaClos}-free rules (@{text Assoc}, @{text
  DApp}) delegate their structural "reduces one level inside its own
  represented redex" case directly to @{text
  FREnv_BetaSigma_Assoc_Peak.frenv_assoc_peak_join} / @{text
  FREnv_BetaSigma_DApp_Peak.frenv_dapp_peak_join}, since those lemmas'
  own @{text "App (Eps _) _"}/@{text "App (Eps (App _ _)) _"} wrapping
  convention matches exactly. @{text BetaClos}'s own analogous case does
  \<^emph>\<open>not\<close> match either convention (its left-hand side @{text
  "App (Eps (Lam x M)) L"} sits one level shallower, with no further
  enclosing @{text Eps}), so it is handled inline instead.
\<close>

lemma frenv_id_not_from_step: "\<not> (Id \<rightarrow>\<beta>\<sigma> X)"
proof
  assume "Id \<rightarrow>\<beta>\<sigma> X"
  then show False by (cases rule: beta_sigma_step.cases)
qed

lemma frenv_var_not_from_step: "\<not> (Var x \<rightarrow>\<beta>\<sigma> X)"
proof
  assume "Var x \<rightarrow>\<beta>\<sigma> X"
  then show False by (cases rule: beta_sigma_step.cases)
qed

lemma beta_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Lam x M) N"
  shows "\<exists>K. App (Eps M) (Ext N x Id) \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: x M N rule: beta_sigma_step.induct)
  case (Beta x1 M1 N1)
  then have eq: "x = x1" "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Lam x M = P" "N = Q" by auto
  have "Lam x M \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq(1) .
  then obtain M' where PM': "P' = Lam x M'" and stepM: "M \<rightarrow>\<beta>\<sigma> M'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "App (Eps M) (Ext N x Id) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M') (Ext N x Id)"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM]]])
  have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M') (Ext N x Id)"
    unfolding PM' eq(2) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
  from l r show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Lam x M = P" "N = Q" by auto
  have l: "App (Eps M) (Ext N x Id) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext Q' x Id)"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnL [OF step]]])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext Q' x Id)"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
  from l r show ?case by blast
qed simp_all

lemma betaClos_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (App (Eps (Lam x M)) L) N"
  shows "\<exists>K. App (Eps M) (Ext N x L) \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: x M L N rule: beta_sigma_step.induct)
  case (BetaClos x1 M1 L1 N1)
  then have eq: "x = x1" "M = M1" "L = L1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  from AppL have step0: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "App (Eps (Lam x M)) L = P" "N = Q" by auto
  have step1: "App (Eps (Lam x M)) L \<rightarrow>\<beta>\<sigma> P'" using step0 unfolding eq(1) .
  from step1 show ?case
  proof (cases rule: beta_sigma_step.cases)
    case IdR
    \<comment> \<open>C1: @{text L} is @{text Id}. The direct target
        @{text "App (Eps M) (Ext N x L)"} is already
        @{text "App (Eps M) (Ext N x Id)"} once @{text L} is substituted
        -- exactly what firing @{text IdR} then @{text Beta} reaches, so
        no further reduction is needed on this side.\<close>
    then have Leq: "L = Id" and P'eq: "P' = Lam x M" by auto
    have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext N x L)"
      unfolding P'eq eq(2) [symmetric] Leq by (rule bs_step_into_steps [OF beta_sigma_step.Beta])
    from r show ?thesis using rtranclp.rtrancl_refl by blast
  next
    case (AppL P0')
    \<comment> \<open>Structural: the @{text Lam}'s body @{text M} reduces.\<close>
    then have step2: "Eps (Lam x M) \<rightarrow>\<beta>\<sigma> P0'" and P'eq: "P' = App P0' L" by auto
    from step2 obtain W where P0'eq: "P0' = Eps W" and stepLxM: "Lam x M \<rightarrow>\<beta>\<sigma> W"
      by (cases rule: beta_sigma_step.cases) auto
    from stepLxM obtain M' where PM': "W = Lam x M'" and stepM: "M \<rightarrow>\<beta>\<sigma> M'"
      by (cases rule: beta_sigma_step.cases) auto
    have l: "App (Eps M) (Ext N x L) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M') (Ext N x L)"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM]]])
    have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M') (Ext N x L)"
      unfolding P'eq P0'eq PM' eq(2) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
    from l r show ?thesis by blast
  next
    case (AppR L')
    \<comment> \<open>Structural: @{text L} reduces.\<close>
    then have stepL: "L \<rightarrow>\<beta>\<sigma> L'" and P'eq: "P' = App (Eps (Lam x M)) L'" by auto
    have l: "App (Eps M) (Ext N x L) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext N x L')"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnR [OF stepL]]])
    have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext N x L')"
      unfolding P'eq eq(2) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
    from l r show ?thesis by blast
  qed
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "App (Eps (Lam x M)) L = P" "N = Q" by auto
  have l: "App (Eps M) (Ext N x L) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext Q' x L)"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnL [OF step]]])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M) (Ext Q' x L)"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
  from l r show ?case by blast
qed simp_all

lemma assoc_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (App (Eps L) M)) N"
  shows "\<exists>K. App (Eps L) (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: L M N rule: beta_sigma_step.induct)
  case (Assoc L1 M1 N1)
  then have eq: "L = L1" "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (DApp M1 N1 L1)
  \<comment> \<open>R2: @{text "App (Eps L) M"} is itself @{text DApp}-shaped.\<close>
  then have eq: "M1 = Eps L" "N1 = M" "L1 = N" by auto
  have r: "App (App (Eps M1) L1) (App (Eps N1) L1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L) (App (Eps M) N)"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (IdR P)
  \<comment> \<open>R3: @{text N} is @{text Id}.\<close>
  then have eq: "P = App (Eps L) M" "N = Id" by auto
  have l: "App (Eps L) (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L) M"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdR]])
  from l show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (AppL P P' Q)
  from AppL have step0: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (App (Eps L) M) = P" "N = Q" by auto
  have "Eps (App (Eps L) M) \<rightarrow>\<beta>\<sigma> P'" using step0 unfolding eq(1) .
  then obtain W where PW: "P' = Eps W" and stepW: "App (Eps L) M \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from frenv_assoc_peak_join [OF stepW refl, of N]
  obtain K where K1: "App (Eps W) N \<rightarrow>\<beta>\<sigma>\<^sup>* K" and K2: "App (Eps L) (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* K"
    by blast
  have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* K" unfolding PW eq(2) [symmetric] using K1 .
  from K2 r show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps (App (Eps L) M) = P" "N = Q" by auto
  have l: "App (Eps L) (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L) (App (Eps M) Q')"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.AppR [OF step]]])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L) (App (Eps M) Q')"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  from l r show ?case by blast
qed simp_all

lemma idL_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps Id) M"
  shows "\<exists>K. M \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: M rule: beta_sigma_step.induct)
  case (IdL M1)
  then have eq: "M = M1" by auto
  show ?case unfolding eq by blast
next
  case (IdR P)
  \<comment> \<open>R4: @{text M} is @{text Id}.\<close>
  then have eq: "P = Id" "M = Id" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  \<comment> \<open>@{text "Eps Id"} can never reduce, since @{text Id} is irreducible.\<close>
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps Id = P" by auto
  have "Eps Id \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq .
  then obtain Id' where "Id \<rightarrow>\<beta>\<sigma> Id'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_id_not_from_step show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps Id = P" "M = Q" by auto
  have l: "M \<rightarrow>\<beta>\<sigma>\<^sup>* Q'" unfolding eq(2) by (rule bs_step_into_steps [OF step])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* Q'" unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.IdL])
  from l r show ?case by blast
qed simp_all

lemma idR_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps M) Id"
  shows "\<exists>K. M \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: M rule: beta_sigma_step.induct)
  case (IdR M1)
  then have eq: "M = M1" by auto
  show ?case unfolding eq by blast
next
  case (Assoc L1 M1 N1)
  \<comment> \<open>R3, from the other side.\<close>
  then have eq: "M = App (Eps L1) M1" "N1 = Id" by auto
  have r: "App (Eps L1) (App (Eps M1) N1) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) M1"
    unfolding eq(2) by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdR]])
  from r show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (IdL P)
  \<comment> \<open>R4, from the other side.\<close>
  then have eq: "M = Id" "P = Id" by auto
  show ?case unfolding eq by blast
next
  case (DExtn L1 z M1 N1)
  \<comment> \<open>R5, from the other side.\<close>
  then have eq: "M = Ext L1 z M1" "N1 = Id" by auto
  have r: "Ext (App (Eps L1) N1) z (App (Eps M1) N1) \<rightarrow>\<beta>\<sigma>\<^sup>* Ext L1 z M1"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.IdR]]
              bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.IdR]]])
  from r show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (DApp M1 N1 L1)
  \<comment> \<open>R6, from the other side.\<close>
  then have eq: "M = App M1 N1" "L1 = Id" by auto
  have r: "App (App (Eps M1) L1) (App (Eps N1) L1) \<rightarrow>\<beta>\<sigma>\<^sup>* App M1 N1"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.IdR]]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdR]]])
  from r show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (EpsEps M1 N1)
  \<comment> \<open>R1, from the other side.\<close>
  then have eq: "M = Eps M1" "N1 = Id" by auto
  show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (AppL P P' Q)
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps M = P" "Id = Q" by auto
  have "Eps M \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq(1) .
  then obtain M' where PM': "P' = Eps M'" and stepM: "M \<rightarrow>\<beta>\<sigma> M'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M'" by (rule bs_step_into_steps [OF stepM])
  have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* M'"
    unfolding PM' eq(2) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.IdR])
  from l r show ?case by blast
next
  case (AppR Q Q' P)
  \<comment> \<open>@{text Id} can never reduce.\<close>
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Id = Q" by auto
  have "Id \<rightarrow>\<beta>\<sigma> Q'" using step unfolding eq .
  with frenv_id_not_from_step show ?case by blast
qed simp_all

lemma epsEps_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (Eps M)) N"
  shows "\<exists>K. Eps M \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: M N rule: beta_sigma_step.induct)
  case (EpsEps M1 N1)
  then have eq: "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (IdR P)
  \<comment> \<open>R1.\<close>
  then have eq: "P = Eps M" "N = Id" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (Eps M) = P" "N = Q" by auto
  have "Eps (Eps M) \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq(1) .
  then obtain M' where PM': "P' = Eps M'" and stepEM: "Eps M \<rightarrow>\<beta>\<sigma> M'"
    by (cases rule: beta_sigma_step.cases) auto
  from stepEM obtain M'' where M'eq: "M' = Eps M''" and stepM: "M \<rightarrow>\<beta>\<sigma> M''"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "Eps M \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M''" by (rule bs_step_into_steps [OF beta_sigma_step.EnvAbst [OF stepM]])
  have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M''"
    unfolding PM' M'eq eq(2) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  from l r show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have eq: "Eps (Eps M) = P" "N = Q" by auto
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  from r show ?case using rtranclp.rtrancl_refl by blast
qed simp_all

lemma dExtn_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (Ext L x M)) N"
  shows "\<exists>K. Ext (App (Eps L) N) x (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: L x M N rule: beta_sigma_step.induct)
  case (DExtn L1 x1 M1 N1)
  then have eq: "L = L1" "x = x1" "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (IdR P)
  \<comment> \<open>R5.\<close>
  then have eq: "P = Ext L x M" "N = Id" by auto
  have l: "Ext (App (Eps L) N) x (App (Eps M) N) \<rightarrow>\<beta>\<sigma>\<^sup>* Ext L x M"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.IdR]]
              bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.IdR]]])
  from l show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (AppL P P' Q)
  from AppL have step0: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (Ext L x M) = P" "N = Q" by auto
  have "Eps (Ext L x M) \<rightarrow>\<beta>\<sigma> P'" using step0 unfolding eq(1) .
  then obtain W where PW: "P' = Eps W" and stepEW: "Ext L x M \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from stepEW show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL L1')
    then have stepL: "L \<rightarrow>\<beta>\<sigma> L1'" and Weq: "W = Ext L1' x M" by auto
    have l: "Ext (App (Eps L) N) x (App (Eps M) N)
               \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1') N) x (App (Eps M) N)"
      by (rule bs_step_into_steps
            [OF beta_sigma_step.ExtnL [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepL]]]])
    have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1') N) x (App (Eps M) N)"
      unfolding PW Weq eq(2) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
    from l r show ?thesis by blast
  next
    case (ExtnR M1')
    then have stepM: "M \<rightarrow>\<beta>\<sigma> M1'" and Weq: "W = Ext L x M1'" by auto
    have l: "Ext (App (Eps L) N) x (App (Eps M) N)
               \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L) N) x (App (Eps M1') N)"
      by (rule bs_step_into_steps
            [OF beta_sigma_step.ExtnR [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepM]]]])
    have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L) N) x (App (Eps M1') N)"
      unfolding PW Weq eq(2) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
    from l r show ?thesis by blast
  qed
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps (Ext L x M) = P" "N = Q" by auto
  have l: "Ext (App (Eps L) N) x (App (Eps M) N)
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L) Q') x (App (Eps M) Q')"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.AppR [OF step]]]
              bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.AppR [OF step]]]])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L) Q') x (App (Eps M) Q')"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
  from l r show ?case by blast
qed simp_all

lemma varRef_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (Var x)) (Ext M x N)"
  shows "\<exists>K. M \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: x M N rule: beta_sigma_step.induct)
  case (VarRef x1 M1 N1)
  then have eq: "x = x1" "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  \<comment> \<open>@{text "Eps (Var x)"} can never reduce, since @{text "Var x"} is
      irreducible.\<close>
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (Var x) = P" by auto
  have "Eps (Var x) \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq .
  then obtain V' where "Var x \<rightarrow>\<beta>\<sigma> V'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_var_not_from_step show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps (Var x) = P" "Ext M x N = Q" by auto
  have "Ext M x N \<rightarrow>\<beta>\<sigma> Q'" using step unfolding eq(2) .
  then show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL M1')
    then have stepM: "M \<rightarrow>\<beta>\<sigma> M1'" and Q'eq: "Q' = Ext M1' x N" by auto
    have l: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M1'" by (rule bs_step_into_steps [OF stepM])
    have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* M1'"
      unfolding Q'eq eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.VarRef])
    from l r show ?thesis by blast
  next
    case (ExtnR N1')
    then have Q'eq: "Q' = Ext M x N1'" by auto
    have l: "M \<rightarrow>\<beta>\<sigma>\<^sup>* M" by (rule rtranclp.rtrancl_refl)
    have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* M"
      unfolding Q'eq eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.VarRef])
    from l r show ?thesis by blast
  qed
qed simp_all

lemma varSkip_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (Var y)) (Ext M x N)" and "x \<noteq> y"
  shows "\<exists>K. App (Eps (Var y)) N \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: y M x N rule: beta_sigma_step.induct)
  case (VarSkip x1 y1 M1 N1)
  then have eq: "x1 = x" "y1 = y" "M = M1" "N = N1" by auto
  show ?case unfolding eq by blast
next
  case (AppL P P' Q)
  \<comment> \<open>@{text "Eps (Var y)"} can never reduce, since @{text "Var y"} is
      irreducible.\<close>
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (Var y) = P" by auto
  have "Eps (Var y) \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq .
  then obtain V' where "Var y \<rightarrow>\<beta>\<sigma> V'"
    by (cases rule: beta_sigma_step.cases) auto
  with frenv_var_not_from_step show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps (Var y) = P" "Ext M x N = Q"
    and neq: "x \<noteq> y" by auto
  have "Ext M x N \<rightarrow>\<beta>\<sigma> Q'" using step unfolding eq(2) .
  then show ?case
  proof (cases rule: beta_sigma_step.cases)
    case (ExtnL M1')
    then have Q'eq: "Q' = Ext M1' x N" by auto
    have l: "App (Eps (Var y)) N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N" by (rule rtranclp.rtrancl_refl)
    have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N"
      unfolding Q'eq eq(1) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]])
    from l r show ?thesis by blast
  next
    case (ExtnR N1')
    then have stepN: "N \<rightarrow>\<beta>\<sigma> N1'" and Q'eq: "Q' = Ext M x N1'" by auto
    have l: "App (Eps (Var y)) N \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N1'"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF stepN]])
    have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) N1'"
      unfolding Q'eq eq(1) [symmetric]
      by (rule bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]])
    from l r show ?thesis by blast
  qed
qed simp_all

lemma dApp_root_peak:
  assumes "X \<rightarrow>\<beta>\<sigma> N2" and "X = App (Eps (App M N)) L"
  shows "\<exists>K. App (App (Eps M) L) (App (Eps N) L) \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> N2 \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: M N L rule: beta_sigma_step.induct)
  case (DApp M1 N1 L1)
  then have eq: "M = M1" "N = N1" "L = L1" by auto
  show ?case unfolding eq by blast
next
  case (Assoc P Q R)
  \<comment> \<open>R2, from the @{text DApp} side: @{text "App M N"} is itself
      @{text Assoc}-shaped.\<close>
  then have eq: "M = Eps P" "N = Q" "L = R" by auto
  have r: "App (App (Eps M) L) (App (Eps N) L) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) (App (Eps Q) R)"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (IdR P)
  \<comment> \<open>R6.\<close>
  then have eq: "P = App M N" "L = Id" by auto
  have l: "App (App (Eps M) L) (App (Eps N) L) \<rightarrow>\<beta>\<sigma>\<^sup>* App M N"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.IdR]]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdR]]])
  from l show ?case unfolding eq(1) [symmetric] using rtranclp.rtrancl_refl by blast
next
  case (AppL P P' Q)
  from AppL have step0: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps (App M N) = P" "L = Q" by auto
  have "Eps (App M N) \<rightarrow>\<beta>\<sigma> P'" using step0 unfolding eq(1) .
  then obtain W where PW: "P' = Eps W" and stepW: "App M N \<rightarrow>\<beta>\<sigma> W"
    by (cases rule: beta_sigma_step.cases) auto
  from frenv_dapp_peak_join [OF stepW refl, of L]
  obtain K where K1: "App (Eps W) L \<rightarrow>\<beta>\<sigma>\<^sup>* K"
      and K2: "App (App (Eps M) L) (App (Eps N) L) \<rightarrow>\<beta>\<sigma>\<^sup>* K" by blast
  have r: "App P' Q \<rightarrow>\<beta>\<sigma>\<^sup>* K" unfolding PW eq(2) [symmetric] using K1 .
  from K2 r show ?case by blast
next
  case (AppR Q Q' P)
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps (App M N) = P" "L = Q" by auto
  have l: "App (App (Eps M) L) (App (Eps N) L)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M) Q') (App (Eps N) Q')"
    unfolding eq(2)
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.AppR [OF step]]]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.AppR [OF step]]]])
  have r: "App P Q' \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M) Q') (App (Eps N) Q')"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.DApp])
  from l r show ?case by blast
qed simp_all

end
