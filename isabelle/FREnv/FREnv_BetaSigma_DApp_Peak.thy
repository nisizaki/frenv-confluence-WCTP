theory FREnv_BetaSigma_DApp_Peak
  imports FREnv_BetaSigma_Congruence
begin

text \<open>
  The @{text DApp} critical-pair family for @{text "lambda_FREnv"} (docs
  file @{text "docs/frenv-beta-sigma-local-confluence.md"}, \<section>3.3,
  critical pairs D1-D10, plus the same-root @{text "R2/C1"} overlaps of
  \<section>3.1 that involve @{text DApp} directly; roadmap item 4).

  @{text DApp}'s left-hand side is @{text "App (Eps (App U V)) S"}: the
  represented application @{text "App U V"} is not composition-shaped, so
  this family is richer than @{text FREnv_BetaSigma_Assoc_Peak}'s: since
  @{text "lambda_FREnv"}'s own @{text Beta}/@{text BetaClos} both have an
  @{text App}-headed left-hand side, they can fire directly on
  @{text "App U V"} itself (@{text D1}/@{text D2}), and if @{text U} is
  @{text Eps}-headed, @{text "App U V"} can \<^emph>\<open>also\<close> match any of the
  eight non-beta base rules directly (@{text D3}-@{text D10}, one per
  rule, mirroring @{text FREnv_BetaSigma_Assoc_Peak.frenv_assoc_peak_join}
  itself once the redundant outer @{text Eps} is stripped via @{text
  "Eps-eps"}).

  Every critical pair in which @{text DApp} fires at the root against a
  step inside its own represented application has the shape
  @{text "App (Eps Y) S  \<leftarrow>  App (Eps (App U V)) S  \<rightarrow>  App (App (Eps U) S) (App (Eps V) S)"}
  where @{term "App U V \<rightarrow>\<beta>\<sigma> Y"}. This single lemma joins all of them.
\<close>

lemma frenv_dapp_peak_join:
  assumes "X \<rightarrow>\<beta>\<sigma> Y" and "X = App U V"
  shows "\<exists>K. App (Eps Y) S \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> App (App (Eps U) S) (App (Eps V) S) \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: U V rule: beta_sigma_step.induct)
  case (Beta x M1 N1)
  \<comment> \<open>D1: @{text U} is @{text Lam}-shaped.\<close>
  then have eq: "U = Lam x M1" "V = N1" by auto
  have l: "App (Eps (App (Eps M1) (Ext N1 x Id))) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x S)"
  proof -
    have "App (Eps (App (Eps M1) (Ext N1 x Id))) S
            \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (App (Eps (Ext N1 x Id)) S)"
      by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x (App (Eps Id) S))"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x S)"
      by (rule bs_step_into_steps
            [OF beta_sigma_step.AppR [OF beta_sigma_step.ExtnR [OF beta_sigma_step.IdL]]])
    finally show ?thesis .
  qed
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x S)"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
  from l r show ?case by blast
next
  case (BetaClos x M1 L1 N1)
  \<comment> \<open>D2: @{text U} is @{text "App (Eps (Lam x M)) L"}-shaped.\<close>
  then have eq: "U = App (Eps (Lam x M1)) L1" "V = N1" by auto
  have l: "App (Eps (App (Eps M1) (Ext N1 x L1))) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x (App (Eps L1) S))"
  proof -
    have "App (Eps (App (Eps M1) (Ext N1 x L1))) S
            \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (App (Eps (Ext N1 x L1)) S)"
      by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x (App (Eps L1) S))"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]])
    finally show ?thesis .
  qed
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x (App (Eps L1) S))"
  proof -
    have "App (App (Eps (App (Eps (Lam x M1)) L1)) S) (App (Eps N1) S)
            \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps (Lam x M1)) (App (Eps L1) S)) (App (Eps N1) S)"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.Assoc]])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) (Ext (App (Eps N1) S) x (App (Eps L1) S))"
      by (rule bs_step_into_steps [OF beta_sigma_step.BetaClos])
    finally show ?thesis unfolding eq .
  qed
  from l r show ?case by blast
next
  case (Assoc L1 M1 N1)
  \<comment> \<open>D4: @{text U} is @{text "Eps (App (Eps L) M)"}-shaped
      (@{text "Assoc"} fires on @{text "App U V"} directly).\<close>
  then have eq: "U = Eps (App (Eps L1) M1)" "V = N1" by auto
  have l: "App (Eps (App (Eps L1) (App (Eps M1) N1))) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) (App (Eps N1) S))"
  proof -
    have "App (Eps (App (Eps L1) (App (Eps M1) N1))) S
            \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps (App (Eps M1) N1)) S)"
      by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) (App (Eps N1) S))"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.Assoc]])
    finally show ?thesis .
  qed
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) (App (Eps N1) S))"
  proof -
    have "App (App (Eps (Eps (App (Eps L1) M1))) S) (App (Eps N1) S)
            \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (App (Eps L1) M1)) (App (Eps N1) S)"
      by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]])
    also have "\<dots> \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps L1) (App (Eps M1) (App (Eps N1) S))"
      by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
    finally show ?thesis unfolding eq .
  qed
  from l r show ?case by blast
next
  case (IdL M1)
  \<comment> \<open>D5: @{text U} is @{text "Eps Id"}-shaped.\<close>
  then have eq: "U = Eps Id" "V = M1" by auto
  have r: "App (App (Eps U) S) (App (Eps V) S) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) S"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              bs_step_into_steps [OF beta_sigma_step.IdL]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (IdR M1)
  \<comment> \<open>D6: @{text V} is @{text Id} and @{text U} is @{text Eps}-shaped.\<close>
  then have eq: "U = Eps M1" "V = Id" by auto
  have r: "App (App (Eps U) S) (App (Eps V) S) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps M1) S"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdL]]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (DExtn L1 z M1 N1)
  \<comment> \<open>D7: @{text U} is @{text "Eps (Ext L z M)"}-shaped.\<close>
  then have eq: "U = Eps (Ext L1 z M1)" "V = N1" by auto
  have l: "App (Eps (Ext (App (Eps L1) N1) z (App (Eps M1) N1))) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) (App (Eps N1) S)) z (App (Eps M1) (App (Eps N1) S))"
  proof -
    have s1: "App (Eps (Ext (App (Eps L1) N1) z (App (Eps M1) N1))) S
                \<rightarrow>\<beta>\<sigma> Ext (App (Eps (App (Eps L1) N1)) S) z (App (Eps (App (Eps M1) N1)) S)"
      by (rule beta_sigma_step.DExtn)
    have s2: "Ext (App (Eps (App (Eps L1) N1)) S) z (App (Eps (App (Eps M1) N1)) S)
                \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) (App (Eps N1) S)) z (App (Eps M1) (App (Eps N1) S))"
      by (rule rtranclp_trans
            [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.Assoc]]
                bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.Assoc]]])
    from rtranclp_trans [OF bs_step_into_steps [OF s1] s2] show ?thesis .
  qed
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps L1) (App (Eps N1) S)) z (App (Eps M1) (App (Eps N1) S))"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              bs_step_into_steps [OF beta_sigma_step.DExtn]])
  from l r show ?case by blast
next
  case (VarRef z P1 Q1)
  \<comment> \<open>D8: @{text U} is @{text "Eps (Var z)"}-shaped.\<close>
  then have eq: "U = Eps (Var z)" "V = Ext P1 z Q1" by auto
  have r: "App (App (Eps U) S) (App (Eps V) S) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P1) S"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              rtranclp_trans
               [OF bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]]
                   bs_step_into_steps [OF beta_sigma_step.VarRef]]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (VarSkip x y P1 Q1)
  \<comment> \<open>D9: @{text U} is @{text "Eps (Var y)"}-shaped, @{text "x \<noteq> y"}.\<close>
  then have neq: "x \<noteq> y" and eq: "U = Eps (Var y)" "V = Ext P1 x Q1" by auto
  have l: "App (Eps (App (Eps (Var y)) Q1)) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) (App (Eps Q1) S)"
    by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) (App (Eps Q1) S)"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              rtranclp_trans
               [OF bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]]
                   bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]]]])
  from l r show ?case by blast
next
  case (DApp M1 N1 L1)
  \<comment> \<open>D10: @{text U} is @{text "Eps (App M N)"}-shaped.\<close>
  then have eq: "U = Eps (App M1 N1)" "V = L1" by auto
  have l: "App (Eps (App (App (Eps M1) L1) (App (Eps N1) L1))) S
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M1) (App (Eps L1) S)) (App (Eps N1) (App (Eps L1) S))"
  proof -
    have s1: "App (Eps (App (App (Eps M1) L1) (App (Eps N1) L1))) S
                \<rightarrow>\<beta>\<sigma> App (App (Eps (App (Eps M1) L1)) S) (App (Eps (App (Eps N1) L1)) S)"
      by (rule beta_sigma_step.DApp)
    have s2: "App (App (Eps (App (Eps M1) L1)) S) (App (Eps (App (Eps N1) L1)) S)
                \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M1) (App (Eps L1) S)) (App (Eps N1) (App (Eps L1) S))"
      by (rule rtranclp_trans
            [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.Assoc]]
                bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.Assoc]]])
    from rtranclp_trans [OF bs_step_into_steps [OF s1] s2] show ?thesis .
  qed
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps M1) (App (Eps L1) S)) (App (Eps N1) (App (Eps L1) S))"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              bs_step_into_steps [OF beta_sigma_step.DApp]])
  from l r show ?case by blast
next
  case (EpsEps M1 N1)
  \<comment> \<open>D3: @{text U} is @{text "Eps (Eps M)"}-shaped. As in the @{text
      Assoc} family's own @{text EpsEps} case, the target
      @{text "Y = Eps M1"} is itself @{text Eps}-wrapped, so the
      left-hand side also needs a genuine @{text EpsEps} step.\<close>
  then have eq: "U = Eps (Eps M1)" "V = N1" by auto
  have l: "App (Eps (Eps M1)) S \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M1"
    by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  have r: "App (App (Eps U) S) (App (Eps V) S) \<rightarrow>\<beta>\<sigma>\<^sup>* Eps M1"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EpsEps]]
              bs_step_into_steps [OF beta_sigma_step.EpsEps]])
  from l r show ?case by blast
next
  case (AppL U1 U1' V1)
  \<comment> \<open>Structural: the inner step reduces @{text U} directly.\<close>
  from AppL have step: "U1 \<rightarrow>\<beta>\<sigma> U1'" and eq: "U = U1" "V = V1" by auto
  have l: "App (Eps (App U1' V1)) S \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps U1') S) (App (Eps V1) S)"
    by (rule bs_step_into_steps [OF beta_sigma_step.DApp])
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps U1') S) (App (Eps V1) S)"
    unfolding eq
    by (rule bs_step_into_steps
          [OF beta_sigma_step.AppL [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF step]]]])
  from l r show ?case by blast
next
  case (AppR V1 V1' U1)
  \<comment> \<open>Structural: the inner step reduces @{text V} directly.\<close>
  from AppR have step: "V1 \<rightarrow>\<beta>\<sigma> V1'" and eq: "U = U1" "V = V1" by auto
  have l: "App (Eps (App U1 V1')) S \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps U1) S) (App (Eps V1') S)"
    by (rule bs_step_into_steps [OF beta_sigma_step.DApp])
  have r: "App (App (Eps U) S) (App (Eps V) S)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps U1) S) (App (Eps V1') S)"
    unfolding eq
    by (rule bs_step_into_steps
          [OF beta_sigma_step.AppR [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF step]]]])
  from l r show ?case by blast
qed simp_all

end
