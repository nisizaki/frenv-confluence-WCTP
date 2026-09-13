theory FREnv_BetaSigma_Assoc_Peak
  imports FREnv_BetaSigma_Congruence
begin

text \<open>
  The @{text Assoc} critical-pair family for @{text "lambda_FREnv"}
  (docs file @{text "docs/frenv-beta-sigma-local-confluence.md"},
  \<section>3.2, critical pairs A1-A8; roadmap item 4), mirroring
  @{text "EnvEps.EnvEps_Sigma_Assoc_Peak.assoc_peak_join"} under the
  substitution @{text "Comp X Y \<mapsto> App (Eps X) Y"} (composition is not a
  syntactic primitive in @{text "lambda_FREnv"}; it is represented as
  @{text "App (Eps X) Y"}).

  Every critical pair in which @{text Assoc} fires at the root against a
  step inside its own left argument has the shape
  @{text "App (Eps Y) W  \<leftarrow>  App (Eps (App (Eps U) V)) W  \<rightarrow>  App (Eps U) (App (Eps V) W)"}
  where @{term "App (Eps U) V \<rightarrow>\<beta>\<sigma> Y"}. This single lemma joins all of
  them, by inverting that inner step.
\<close>

lemma frenv_assoc_peak_join:
  assumes "X \<rightarrow>\<beta>\<sigma> Y" and "X = App (Eps U) V"
  shows "\<exists>K. App (Eps Y) W \<rightarrow>\<beta>\<sigma>\<^sup>* K \<and> App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* K"
  using assms
proof (induction arbitrary: U V rule: beta_sigma_step.induct)
  case (Assoc P Q R)
  \<comment> \<open>A2: @{text U} is itself @{text Assoc}-shaped.\<close>
  then have eq: "U = App (Eps P) Q" "V = R" by auto
  have l: "App (Eps (App (Eps P) (App (Eps Q) R))) W
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) (App (Eps Q) (App (Eps R) W))"
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.Assoc]
              bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.Assoc]]])
  have r: "App (Eps U) (App (Eps V) W)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) (App (Eps Q) (App (Eps R) W))"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  from l r show ?case by blast
next
  case (IdL P)
  \<comment> \<open>A3: @{text U} is @{text Id}.\<close>
  then have eq: "U = Id" "V = P" by auto
  have "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) W"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.IdL])
  then show ?case using rtranclp.rtrancl_refl by blast
next
  case (IdR P)
  \<comment> \<open>A4: @{text V} is @{text Id}.\<close>
  then have eq: "U = P" "V = Id" by auto
  have "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) W"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.IdL]])
  then show ?case using rtranclp.rtrancl_refl by blast
next
  case (DExtn P z Q R)
  \<comment> \<open>A5: @{text U} is @{text Ext}-shaped.\<close>
  then have eq: "U = Ext P z Q" "V = R" by auto
  have l: "App (Eps (Ext (App (Eps P) R) z (App (Eps Q) R))) W
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps P) (App (Eps R) W)) z (App (Eps Q) (App (Eps R) W))"
  proof -
    have s1: "App (Eps (Ext (App (Eps P) R) z (App (Eps Q) R))) W
                \<rightarrow>\<beta>\<sigma> Ext (App (Eps (App (Eps P) R)) W) z (App (Eps (App (Eps Q) R)) W)"
      by (rule beta_sigma_step.DExtn)
    have s2: "Ext (App (Eps (App (Eps P) R)) W) z (App (Eps (App (Eps Q) R)) W)
                \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps P) (App (Eps R) W)) z (App (Eps Q) (App (Eps R) W))"
      by (rule rtranclp_trans
            [OF bs_step_into_steps [OF beta_sigma_step.ExtnL [OF beta_sigma_step.Assoc]]
                bs_step_into_steps [OF beta_sigma_step.ExtnR [OF beta_sigma_step.Assoc]]])
    from rtranclp_trans [OF bs_step_into_steps [OF s1] s2] show ?thesis .
  qed
  have r: "App (Eps U) (App (Eps V) W)
             \<rightarrow>\<beta>\<sigma>\<^sup>* Ext (App (Eps P) (App (Eps R) W)) z (App (Eps Q) (App (Eps R) W))"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.DExtn])
  from l r show ?case by blast
next
  case (VarRef z P Q)
  \<comment> \<open>A6: @{text U} is a variable matching the extension's binding.\<close>
  then have eq: "U = Var z" "V = Ext P z Q" by auto
  have r: "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps P) W"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]]
              bs_step_into_steps [OF beta_sigma_step.VarRef]])
  from r show ?case using rtranclp.rtrancl_refl by blast
next
  case (VarSkip x y P Q)
  \<comment> \<open>A7: @{text U} is a variable not matching the extension's binding.\<close>
  then have neq: "x \<noteq> y" and eq: "U = Var y" "V = Ext P x Q" by auto
  have l: "App (Eps (App (Eps (Var y)) Q)) W
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) (App (Eps Q) W)"
    by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  have r: "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps (Var y)) (App (Eps Q) W)"
    unfolding eq
    by (rule rtranclp_trans
          [OF bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.DExtn]]
              bs_step_into_steps [OF beta_sigma_step.VarSkip [OF neq]]])
  from l r show ?case by blast
next
  case (DApp P Q R)
  \<comment> \<open>A8: @{text U} is @{text App}-shaped.\<close>
  then have eq: "U = App P Q" "V = R" by auto
  have l: "App (Eps (App (App (Eps P) R) (App (Eps Q) R))) W
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps P) (App (Eps R) W)) (App (Eps Q) (App (Eps R) W))"
  proof -
    have s1: "App (Eps (App (App (Eps P) R) (App (Eps Q) R))) W
                \<rightarrow>\<beta>\<sigma> App (App (Eps (App (Eps P) R)) W) (App (Eps (App (Eps Q) R)) W)"
      by (rule beta_sigma_step.DApp)
    have s2: "App (App (Eps (App (Eps P) R)) W) (App (Eps (App (Eps Q) R)) W)
                \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps P) (App (Eps R) W)) (App (Eps Q) (App (Eps R) W))"
      by (rule rtranclp_trans
            [OF bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.Assoc]]
                bs_step_into_steps [OF beta_sigma_step.AppR [OF beta_sigma_step.Assoc]]])
    from rtranclp_trans [OF bs_step_into_steps [OF s1] s2] show ?thesis .
  qed
  have r: "App (Eps U) (App (Eps V) W)
             \<rightarrow>\<beta>\<sigma>\<^sup>* App (App (Eps P) (App (Eps R) W)) (App (Eps Q) (App (Eps R) W))"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.DApp])
  from l r show ?case by blast
next
  case (EpsEps P R)
  \<comment> \<open>A1: @{text U} is @{text Eps}-shaped. The target @{text "Y = Eps P"}
      is itself doubly-@{text Eps}-wrapped through @{text U}, so the
      left-hand side also needs a genuine @{text EpsEps} step, not
      reflexivity.\<close>
  then have eq: "U = Eps P" "V = R" by auto
  have l: "App (Eps (Eps P)) W \<rightarrow>\<beta>\<sigma>\<^sup>* Eps P"
    by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  have r: "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* Eps P"
    unfolding eq by (rule bs_step_into_steps [OF beta_sigma_step.EpsEps])
  from l r show ?case by blast
next
  case (AppL P P' Q)
  \<comment> \<open>Structural: the inner step reduces @{text U} (via @{text EnvAbst}
      then @{text AppL}).\<close>
  from AppL have step: "P \<rightarrow>\<beta>\<sigma> P'" and eq: "Eps U = P" "V = Q" by auto
  have "Eps U \<rightarrow>\<beta>\<sigma> P'" using step unfolding eq(1) .
  then obtain U' where PU': "P' = Eps U'" and stepU: "U \<rightarrow>\<beta>\<sigma> U'"
    by (cases rule: beta_sigma_step.cases) auto
  have l: "App (Eps (App P' Q)) W \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps U') (App (Eps V) W)"
    unfolding PU' eq(2) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  have r: "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps U') (App (Eps V) W)"
    by (rule bs_step_into_steps [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF stepU]]])
  from l r show ?case by blast
next
  case (AppR Q Q' P)
  \<comment> \<open>Structural: the inner step reduces @{text V} directly.\<close>
  from AppR have step: "Q \<rightarrow>\<beta>\<sigma> Q'" and eq: "Eps U = P" "V = Q" by auto
  have l: "App (Eps (App P Q')) W \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps U) (App (Eps Q') W)"
    unfolding eq(1) [symmetric] by (rule bs_step_into_steps [OF beta_sigma_step.Assoc])
  have r: "App (Eps U) (App (Eps V) W) \<rightarrow>\<beta>\<sigma>\<^sup>* App (Eps U) (App (Eps Q') W)"
    unfolding eq(2)
    by (rule bs_step_into_steps
          [OF beta_sigma_step.AppR [OF beta_sigma_step.AppL [OF beta_sigma_step.EnvAbst [OF step]]]])
  from l r show ?case by blast
qed simp_all

end
