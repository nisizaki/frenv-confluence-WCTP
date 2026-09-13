theory EnvEps_Beta_Normal_Form_Simulation
  imports EnvEps_Beta_Over_Sigma_Congruence EnvEps_Sigma_Length_Decrease
    EnvEps_Sigma_Nf_Equiv EnvEps_Parallel_Reduction_Simulation
    EnvEps_Parallel_Reduction_Soundness EnvEps_Parallel_Reduction_Composition_Compatibility
begin

text \<open>
  Simulation of @{text "\<rightarrow>\<^sub>\<beta>"} by @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} on @{text "\<sigma>"}-normal
  forms (docs file @{text "docs/enve-beta-normal-form-simulation.md"},
  thesis Theorem 7, presented there as a Lemma; roadmap item 16).

  Strong induction on @{text length_enve}, case-split on the rule of
  @{text "\<rightarrow>\<^sub>\<beta>"} used. The @{text Lam}/@{text Eop}/@{text AppL}/@{text
  AppR}/@{text ExtnL}/@{text ExtnR} congruence cases go through directly
  via the "safe context" lemmas of @{text EnvEps_Beta_Over_Sigma_Congruence}
  and the unconditional @{text sigma_nf} equations of @{text
  EnvEps_Sigma_Nf_Equiv}. @{text Beta} and @{text "Comp\<^sub>\<epsilon>"} fire their
  redex directly via @{text beta_over_sigma_step_Beta}/@{text
  beta_over_sigma_step_CompEps}.

  \<^bold>\<open>Fixed foundational mismatch (@{text BetaClos}).\<close> @{text
  EnvEps_BetaSigma}'s own @{text BetaClos} rule (roadmap item 15) now
  fires on the @{text Comp}-headed @{text "App (Comp (Lam x M) L) N"}
  shape, matching the thesis's own Definition 5 literally. Since @{text
  M} here is arbitrary (not assumed @{text "\<sigma>"}-normal), the case is
  proved by first computing @{text "sigma_nf M"} and @{text "sigma_nf N"}
  explicitly via @{text sigma_nf_Comp_idem_L}/@{text
  sigma_nf_Comp_idem_R}/@{text sigma_nf_Ext}, then case-splitting on
  whether @{text "sigma_nf L"} collapses to @{text Id} -- landing on
  @{text beta_over_sigma_step_Beta} (collapse) or the new @{text
  beta_over_sigma_step_BetaClos} (no collapse), mirroring the analogous
  split in @{text EnvEps_Parallel_Reduction_Soundness}'s @{text
  ParBetaClos} case.

  \<^bold>\<open>Fixed scope gap (@{text CompL}/@{text CompR}).\<close> The docs' own case
  split for this branch (mirroring the eight @{text "\<rightarrow>\<sigma>"} base rules,
  plus a residual "@{text Other}" case) classifies the target shape by
  the *syntactic* form of the fixed partner -- but since @{text M} is
  arbitrary here (not assumed @{text "\<sigma>"}-normal, unlike roadmap items
  19/20), that partner's @{text "\<sigma>"}-normal form need not match its own
  syntactic shape (e.g. a syntactically non-@{text Id} term can still
  @{text "\<sigma>"}-normalize to @{text Id}), so classifying by syntax alone is
  unsound. Rather than re-deriving the docs' rule-by-rule case split
  purely in terms of @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}, both cases instead round-trip through
  @{text "\<Rightarrow>par"}'s already-proven, fully general @{text
  par_step_composition_compatibility} (roadmap item 22, which internally
  handles every @{text sigma_nf}-collapse case exhaustively): the two new
  chain lemmas @{text beta_over_sigma_steps_CompL_general}/@{text
  beta_over_sigma_steps_CompR_general} lift a single-sided @{text
  "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} chain through @{text Comp} by converting each step to @{text
  "\<Rightarrow>par"} (@{text beta_over_sigma_step_simulated_by_par_step}, roadmap
  19), composing via @{text par_step_composition_compatibility}, then
  converting back (@{text par_step_sound_for_beta_over_sigma}, roadmap
  20). No case-split on the fixed partner's shape is needed at this
  theory's level at all -- @{text par_step_composition_compatibility}
  already did that work.
\<close>

lemma beta_over_sigma_steps_CompL_general:
  assumes nP: "is_sigma_normal P" and chain: "P \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* P'" and nQ: "is_sigma_normal Q"
  shows "sigma_nf (Comp P Q) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp P' Q)"
  using chain
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step y z)
  have ny: "is_sigma_normal y" using nP step.hyps(1) by (rule beta_over_sigma_steps_target_normal)
  have parstep: "y \<Rightarrow>par z" using ny step.hyps(2) by (rule beta_over_sigma_step_simulated_by_par_step)
  have parQ: "Q \<Rightarrow>par Q" using nQ by (rule par_step_refl)
  have parcomp: "sigma_nf (Comp y Q) \<Rightarrow>par sigma_nf (Comp z Q)"
    using ny nQ parstep parQ by (rule par_step_composition_compatibility)
  have "sigma_nf (Comp y Q) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp z Q)"
    using is_sigma_normal_sigma_nf parcomp by (rule par_step_sound_for_beta_over_sigma)
  with step.IH show ?case by (rule rtranclp_trans)
qed

lemma beta_over_sigma_steps_CompR_general:
  assumes nP: "is_sigma_normal P" and chain: "Q \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Q'" and nQ: "is_sigma_normal Q"
  shows "sigma_nf (Comp P Q) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp P Q')"
  using chain
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step y z)
  have ny: "is_sigma_normal y" using nQ step.hyps(1) by (rule beta_over_sigma_steps_target_normal)
  have parstep: "y \<Rightarrow>par z" using ny step.hyps(2) by (rule beta_over_sigma_step_simulated_by_par_step)
  have parP: "P \<Rightarrow>par P" using nP by (rule par_step_refl)
  have parcomp: "sigma_nf (Comp P y) \<Rightarrow>par sigma_nf (Comp P z)"
    using nP ny parP parstep by (rule par_step_composition_compatibility)
  have "sigma_nf (Comp P y) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp P z)"
    using is_sigma_normal_sigma_nf parcomp by (rule par_step_sound_for_beta_over_sigma)
  with step.IH show ?case by (rule rtranclp_trans)
qed

theorem beta_step_simulated_by_beta_over_sigma:
  assumes "M \<rightarrow>\<beta> N"
  shows "sigma_nf M \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf N"
  using assms
proof (induction "length_enve M" arbitrary: M N rule: less_induct)
  case less
  from less.prems show ?case
  proof (cases rule: EnvEps_Beta_Step.beta_step.cases)
    case (Beta x M1 M2)
    have step: "App (Lam x (sigma_nf M1)) (sigma_nf M2)
            \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp (sigma_nf M1) (Ext (sigma_nf M2) x Id))"
      by (rule beta_over_sigma_step_Beta)
    have e1: "sigma_nf (Comp M1 (Ext M2 x Id)) = sigma_nf (Comp (sigma_nf M1) (Ext M2 x Id))"
      by (rule sigma_nf_Comp_idem_L)
    have e2: "sigma_nf (Comp (sigma_nf M1) (Ext M2 x Id))
            = sigma_nf (Comp (sigma_nf M1) (sigma_nf (Ext M2 x Id)))"
      by (rule sigma_nf_Comp_idem_R)
    have e3: "sigma_nf (Ext M2 x Id) = Ext (sigma_nf M2) x Id"
      by (simp add: sigma_nf_Ext sigma_nf_of_normal [OF is_sigma_normal.NF_Id])
    have eq: "sigma_nf (Comp M1 (Ext M2 x Id))
            = sigma_nf (Comp (sigma_nf M1) (Ext (sigma_nf M2) x Id))"
      using e1 e2 e3 by simp
    show ?thesis
      unfolding Beta(1,2) sigma_nf_App sigma_nf_Lam eq using step by (rule r_into_rtranclp)
  next
    case (BetaClos x M1 L M2)
    have compEq0: "sigma_nf (Comp (Lam x M1) L) = sigma_nf (Comp (Lam x (sigma_nf M1)) (sigma_nf L))"
    proof -
      have "sigma_nf (Comp (Lam x M1) L) = sigma_nf (Comp (sigma_nf (Lam x M1)) L)"
        by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (Lam x (sigma_nf M1)) L)"
        by (simp add: sigma_nf_Lam)
      also have "\<dots> = sigma_nf (Comp (Lam x (sigma_nf M1)) (sigma_nf L))"
        by (rule sigma_nf_Comp_idem_R)
      finally show ?thesis .
    qed
    have Meq0: "sigma_nf M = App (sigma_nf (Comp (Lam x M1) L)) (sigma_nf M2)"
      unfolding BetaClos(1) by (rule sigma_nf_App)
    have targetEq: "sigma_nf N = sigma_nf (Comp (sigma_nf M1) (Ext (sigma_nf M2) x (sigma_nf L)))"
    proof -
      have "sigma_nf N = sigma_nf (Comp (sigma_nf M1) (Ext M2 x L))"
        unfolding BetaClos(2) by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) (sigma_nf (Ext M2 x L)))"
        by (rule sigma_nf_Comp_idem_R)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) (Ext (sigma_nf M2) x (sigma_nf L)))"
        by (simp add: sigma_nf_Ext)
      finally show ?thesis .
    qed
    show ?thesis
    proof (cases "sigma_nf L = Id")
      case False
      have collapse: "sigma_nf (Comp (Lam x (sigma_nf M1)) (sigma_nf L)) = Comp (Lam x (sigma_nf M1)) (sigma_nf L)"
        by (intro sigma_nf_of_normal is_sigma_normal.NF_CompLam is_sigma_normal_sigma_nf False)
      have Meq: "sigma_nf M = App (Comp (Lam x (sigma_nf M1)) (sigma_nf L)) (sigma_nf M2)"
        using Meq0 compEq0 collapse by simp
      show ?thesis
        unfolding Meq targetEq
        using beta_over_sigma_step_BetaClos by (rule r_into_rtranclp)
    next
      case True
      have collapse: "sigma_nf (Comp (Lam x (sigma_nf M1)) (sigma_nf L)) = Lam x (sigma_nf M1)"
        unfolding True
        by (simp add: sigma_nf_Comp_IdR sigma_nf_of_normal [OF is_sigma_normal.NF_Lam [OF is_sigma_normal_sigma_nf]])
      have Meq: "sigma_nf M = App (Lam x (sigma_nf M1)) (sigma_nf M2)"
        using Meq0 compEq0 collapse by simp
      have targetEq': "sigma_nf N = sigma_nf (Comp (sigma_nf M1) (Ext (sigma_nf M2) x Id))"
        using targetEq True by simp
      show ?thesis
        unfolding Meq targetEq'
        using beta_over_sigma_step_Beta by (rule r_into_rtranclp)
    qed
  next
    case (CompEps M1 M2)
    have step: "App (Eps (sigma_nf M1)) (sigma_nf M2)
              \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))"
      by (rule beta_over_sigma_step_CompEps)
    have e1: "sigma_nf (Comp M1 M2) = sigma_nf (Comp (sigma_nf M1) M2)"
      by (rule sigma_nf_Comp_idem_L)
    have e2: "sigma_nf (Comp (sigma_nf M1) M2) = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))"
      by (rule sigma_nf_Comp_idem_R)
    have eq: "sigma_nf (Comp M1 M2) = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))"
      using e1 e2 by simp
    show ?thesis
      unfolding CompEps(1,2) sigma_nf_App sigma_nf_Eps eq using step by (rule r_into_rtranclp)
  next
    case (AppL M1 M1' M2)
    have lt: "length_enve M1 < length_enve M" unfolding AppL(1) by simp
    have IH1: "sigma_nf M1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M1'" using less.hyps [OF lt AppL(3)] .
    have "App (sigma_nf M1) (sigma_nf M2) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (sigma_nf M1') (sigma_nf M2)"
      using IH1 is_sigma_normal_sigma_nf by (rule beta_over_sigma_steps_AppL)
    then show ?thesis unfolding AppL(1,2) sigma_nf_App .
  next
    case (AppR M2 M2' M1)
    have lt: "length_enve M2 < length_enve M" unfolding AppR(1) by simp
    have IH2: "sigma_nf M2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M2'" using less.hyps [OF lt AppR(3)] .
    have "App (sigma_nf M1) (sigma_nf M2) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (sigma_nf M1) (sigma_nf M2')"
      using IH2 is_sigma_normal_sigma_nf by (rule beta_over_sigma_steps_AppR)
    then show ?thesis unfolding AppR(1,2) sigma_nf_App .
  next
    case (Lam M1 M1' x)
    have lt: "length_enve M1 < length_enve M" unfolding Lam(1) by simp
    have IH1: "sigma_nf M1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M1'" using less.hyps [OF lt Lam(3)] .
    have "Lam x (sigma_nf M1) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Lam x (sigma_nf M1')"
      using IH1 by (rule beta_over_sigma_steps_Lam)
    then show ?thesis unfolding Lam(1,2) sigma_nf_Lam .
  next
    case (ExtnL M1 M1' x M2)
    have lt: "length_enve M1 < length_enve M" unfolding ExtnL(1) by simp
    have IH1: "sigma_nf M1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M1'" using less.hyps [OF lt ExtnL(3)] .
    have "Ext (sigma_nf M1) x (sigma_nf M2) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext (sigma_nf M1') x (sigma_nf M2)"
      using IH1 is_sigma_normal_sigma_nf by (rule beta_over_sigma_steps_ExtnL)
    then show ?thesis unfolding ExtnL(1,2) sigma_nf_Ext .
  next
    case (ExtnR M2 M2' M1 x)
    have lt: "length_enve M2 < length_enve M" unfolding ExtnR(1) by simp
    have IH2: "sigma_nf M2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M2'" using less.hyps [OF lt ExtnR(3)] .
    have "Ext (sigma_nf M1) x (sigma_nf M2) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext (sigma_nf M1) x (sigma_nf M2')"
      using IH2 is_sigma_normal_sigma_nf by (rule beta_over_sigma_steps_ExtnR)
    then show ?thesis unfolding ExtnR(1,2) sigma_nf_Ext .
  next
    case (CompL M1 M1' M2)
    have lt: "length_enve M1 < length_enve M" unfolding CompL(1) by simp
    have IH1: "sigma_nf M1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M1'" using less.hyps [OF lt CompL(3)] .
    have Meq: "sigma_nf M = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))"
    proof -
      have "sigma_nf M = sigma_nf (Comp M1 M2)" unfolding CompL(1) by (rule refl)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) M2)" by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))" by (rule sigma_nf_Comp_idem_R)
      finally show ?thesis .
    qed
    have targetEq: "sigma_nf N = sigma_nf (Comp (sigma_nf M1') (sigma_nf M2))"
    proof -
      have "sigma_nf N = sigma_nf (Comp M1' M2)" unfolding CompL(2) by (rule refl)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1') M2)" by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1') (sigma_nf M2))" by (rule sigma_nf_Comp_idem_R)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding Meq targetEq
      using beta_over_sigma_steps_CompL_general [OF is_sigma_normal_sigma_nf IH1 is_sigma_normal_sigma_nf] .
  next
    case (CompR M2 M2' M1)
    have lt: "length_enve M2 < length_enve M"
      unfolding CompR(1)
    proof -
      have h1: "1 \<le> length_enve M1" using length_pos [of M1] by linarith
      have h2: "1 * (length_enve M2 + 1) \<le> length_enve M1 * (length_enve M2 + 1)"
        using mult_le_mono1 [OF h1] .
      then show "length_enve M2 < length_enve (Comp M1 M2)" by simp
    qed
    have IH2: "sigma_nf M2 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M2'" using less.hyps [OF lt CompR(3)] .
    have Meq: "sigma_nf M = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))"
    proof -
      have "sigma_nf M = sigma_nf (Comp M1 M2)" unfolding CompR(1) by (rule refl)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) M2)" by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2))" by (rule sigma_nf_Comp_idem_R)
      finally show ?thesis .
    qed
    have targetEq: "sigma_nf N = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2'))"
    proof -
      have "sigma_nf N = sigma_nf (Comp M1 M2')" unfolding CompR(2) by (rule refl)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) M2')" by (rule sigma_nf_Comp_idem_L)
      also have "\<dots> = sigma_nf (Comp (sigma_nf M1) (sigma_nf M2'))" by (rule sigma_nf_Comp_idem_R)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding Meq targetEq
      using beta_over_sigma_steps_CompR_general [OF is_sigma_normal_sigma_nf IH2 is_sigma_normal_sigma_nf] .
  next
    case (Eop M1 M1')
    have lt: "length_enve M1 < length_enve M" unfolding Eop(1) by simp
    have IH1: "sigma_nf M1 \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf M1'" using less.hyps [OF lt Eop(3)] .
    have "Eps (sigma_nf M1) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Eps (sigma_nf M1')"
      using IH1 by (rule beta_over_sigma_steps_Eps)
    then show ?thesis unfolding Eop(1,2) sigma_nf_Eps .
  qed
qed

end
