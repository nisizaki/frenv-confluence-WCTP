theory EnvEps_Parallel_Reduction_Simulation
  imports EnvEps_Parallel_Reduction_Reflexivity EnvEps_Beta_Over_Sigma
    EnvEps_Sigma_Nf_Equiv EnvEps_Parallel_Reduction_Composition_Compatibility
begin

text \<open>
  Simulation of @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"} by @{text "\<Rightarrow>par"} (docs file
  @{text "docs/enve-parallel-reduction-simulation.md"}, thesis Theorem 8,
  presented there as a Lemma; roadmap item 19). Strong induction on the
  size of the source term, case-split on the rule of @{text "\<rightarrow>\<^sub>\<beta>"} used
  (mirroring @{text EnvEps_Beta_Normal_Form_Simulation}'s case split),
  using reflexivity (@{text par_step_refl}) on unchanged subterms and the
  "safe context" equations of @{text EnvEps_Sigma_Nf_Equiv}
  (@{text sigma_nf_App} etc.) for the congruence cases. The two @{text
  Comp}-congruence cases (@{text CompL}/@{text CompR}) instead go through
  @{text par_step_composition_compatibility} (roadmap item 22), rewriting
  the source via @{text sigma_nf_of_normal} and the target via
  @{text sigma_nf_Comp_idem_L}/@{text sigma_nf_Comp_idem_R}.

  \<^bold>\<open>Fixed foundational mismatch.\<close> @{text EnvEps_BetaSigma}'s (and
  @{text EnvEps_Beta_Step}'s) own @{text BetaClos} rule (roadmap item 15)
  now fires on the @{text Comp}-headed @{text "App (Comp (Lam x M) L) N"}
  shape, matching the thesis's own Definition 5 literally and, with it,
  @{text par_step.ParBetaClos}'s own source shape. The @{text BetaClos}
  case below is therefore just a direct application of @{text
  par_step.ParBetaClos} to the (already @{text "\<sigma>"}-normal) pieces of the
  source, exactly like every other redex-firing case; no gap remains.
\<close>

lemma beta_over_sigma_step_simulated_by_par_step_aux:
  assumes "is_sigma_normal a" and "a \<rightarrow>\<beta> M"
  shows "a \<Rightarrow>par sigma_nf M"
  using assms
proof (induction "size a" arbitrary: a M rule: less_induct)
    case less
    note na = less.prems(1) and stepM = less.prems(2)
    from stepM na show "a \<Rightarrow>par sigma_nf M"
    proof (cases rule: EnvEps_Beta_Step.beta_step.cases)
      case (Beta x M1 M2)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      show ?thesis
        unfolding Beta(1,2)
        using par_step.ParBeta [OF par_step_refl [OF nM1] par_step_refl [OF nM2]] .
    next
      case (BetaClos x M1 L N)
      then have nCompLam: "is_sigma_normal (Comp (Lam x M1) L)" and nN: "is_sigma_normal N"
        using na by (auto elim: is_sigma_normal.cases)
      then have nM1: "is_sigma_normal M1" and nL: "is_sigma_normal L" and Lnid: "L \<noteq> Id"
        by (auto elim: is_sigma_normal.cases)
      show ?thesis
        unfolding BetaClos(1,2)
        using par_step.ParBetaClos [OF par_step_refl [OF nM1] par_step_refl [OF nN]
                                        par_step_refl [OF nL] Lnid] .
    next
      case (CompEps M1 M2)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      show ?thesis
        unfolding CompEps(1,2)
        using par_step.ParCompEps [OF par_step_refl [OF nM1] par_step_refl [OF nM2]] .
    next
      case (AppL M1 M1' M2)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M1 < size a" unfolding AppL(1) by simp
      have IH1: "M1 \<Rightarrow>par sigma_nf M1'" using less.hyps [OF lt nM1 AppL(3)] .
      have "App M1 M2 \<Rightarrow>par App (sigma_nf M1') M2"
        using IH1 par_step_refl [OF nM2] by (rule par_step.ParApp)
      then show ?thesis
        unfolding AppL(1,2) sigma_nf_App using nM2 by simp
    next
      case (AppR M2 M2' M1)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M2 < size a" unfolding AppR(1) by simp
      have IH2: "M2 \<Rightarrow>par sigma_nf M2'" using less.hyps [OF lt nM2 AppR(3)] .
      have "App M1 M2 \<Rightarrow>par App M1 (sigma_nf M2')"
        using par_step_refl [OF nM1] IH2 by (rule par_step.ParApp)
      then show ?thesis
        unfolding AppR(1,2) sigma_nf_App using nM1 by simp
    next
      case (Lam M1 M1' x)
      then have nM1: "is_sigma_normal M1"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M1 < size a" unfolding Lam(1) by simp
      have IH1: "M1 \<Rightarrow>par sigma_nf M1'" using less.hyps [OF lt nM1 Lam(3)] .
      have "Lam x M1 \<Rightarrow>par Lam x (sigma_nf M1')" using IH1 by (rule par_step.ParLam)
      then show ?thesis unfolding Lam(1,2) sigma_nf_Lam .
    next
      case (ExtnL M1 M1' x M2)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M1 < size a" unfolding ExtnL(1) by simp
      have IH1: "M1 \<Rightarrow>par sigma_nf M1'" using less.hyps [OF lt nM1 ExtnL(3)] .
      have "Ext M1 x M2 \<Rightarrow>par Ext (sigma_nf M1') x M2"
        using IH1 par_step_refl [OF nM2] by (rule par_step.ParExtn)
      then show ?thesis
        unfolding ExtnL(1,2) sigma_nf_Ext using nM2 by simp
    next
      case (ExtnR M2 M2' M1 x)
      then have nM1: "is_sigma_normal M1" and nM2: "is_sigma_normal M2"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M2 < size a" unfolding ExtnR(1) by simp
      have IH2: "M2 \<Rightarrow>par sigma_nf M2'" using less.hyps [OF lt nM2 ExtnR(3)] .
      have "Ext M1 x M2 \<Rightarrow>par Ext M1 x (sigma_nf M2')"
        using par_step_refl [OF nM1] IH2 by (rule par_step.ParExtn)
      then show ?thesis
        unfolding ExtnR(1,2) sigma_nf_Ext using nM1 by simp
    next
      case (CompL M1 M1' M2)
      have nComp: "is_sigma_normal (Comp M1 M2)" using na unfolding CompL(1) .
      have nM1: "is_sigma_normal M1"
        using nComp
        by (cases rule: is_sigma_normal.cases)
           (auto intro: is_sigma_normal.NF_Lam is_sigma_normal.NF_Var)
      have nM2: "is_sigma_normal M2"
        using nComp by (cases rule: is_sigma_normal.cases) auto
      have lt: "size M1 < size a" unfolding CompL(1) by simp
      have IH1: "M1 \<Rightarrow>par sigma_nf M1'" using less.hyps [OF lt nM1 CompL(3)] .
      have "sigma_nf (Comp M1 M2) \<Rightarrow>par sigma_nf (Comp (sigma_nf M1') M2)"
        using nM1 nM2 IH1 par_step_refl [OF nM2]
        by (rule par_step_composition_compatibility)
      then show ?thesis
        unfolding CompL(1,2) using nComp sigma_nf_Comp_idem_L [of M1' M2, symmetric]
        by simp
    next
      case (CompR M2 M2' M1)
      have nComp: "is_sigma_normal (Comp M1 M2)" using na unfolding CompR(1) .
      have nM1: "is_sigma_normal M1"
        using nComp
        by (cases rule: is_sigma_normal.cases)
           (auto intro: is_sigma_normal.NF_Lam is_sigma_normal.NF_Var)
      have nM2: "is_sigma_normal M2"
        using nComp by (cases rule: is_sigma_normal.cases) auto
      have lt: "size M2 < size a" unfolding CompR(1) by simp
      have IH2: "M2 \<Rightarrow>par sigma_nf M2'" using less.hyps [OF lt nM2 CompR(3)] .
      have "sigma_nf (Comp M1 M2) \<Rightarrow>par sigma_nf (Comp M1 (sigma_nf M2'))"
        using nM1 nM2 par_step_refl [OF nM1] IH2
        by (rule par_step_composition_compatibility)
      then show ?thesis
        unfolding CompR(1,2) using nComp sigma_nf_Comp_idem_R [of M1 M2', symmetric]
        by simp
    next
      case (Eop M1 M1')
      then have nM1: "is_sigma_normal M1"
        using na by (auto elim: is_sigma_normal.cases)
      have lt: "size M1 < size a" unfolding Eop(1) by simp
      have IH1: "M1 \<Rightarrow>par sigma_nf M1'" using less.hyps [OF lt nM1 Eop(3)] .
      have "Eps M1 \<Rightarrow>par Eps (sigma_nf M1')" using IH1 by (rule par_step.ParEps)
      then show ?thesis unfolding Eop(1,2) sigma_nf_Eps .
    qed
qed

theorem beta_over_sigma_step_simulated_by_par_step:
  assumes "is_sigma_normal U" and "U \<rightarrow>\<beta>\<bar>\<sigma> U'"
  shows "U \<Rightarrow>par U'"
proof -
  from assms(2) obtain M where M: "U \<rightarrow>\<beta> M" "U' = sigma_nf M"
    using beta_over_sigma_step_iff_sigma_nf by blast
  show ?thesis
    unfolding M(2)
    using beta_over_sigma_step_simulated_by_par_step_aux [OF assms(1) M(1)] .
qed

end
