theory EnvEps_Parallel_Reduction_Triangle_Property
  imports EnvEps_Complete_Development EnvEps_Parallel_Reduction_Composition_Compatibility
begin

text \<open>
  Triangle property of @{text "\<Rightarrow>par"} (docs file
  @{text "docs/enve-parallel-reduction-triangle-property.md"}, thesis
  Theorem 10, presented there as a Lemma; roadmap item 23): every
  @{text "\<Rightarrow>par"}-successor of @{text U} itself @{text "\<Rightarrow>par"}-reduces to
  @{text "cd U"}.

  Strong induction on @{text "length_enve U"} (as in
  @{text EnvEps_Parallel_Reduction_Composition_Compatibility}, roadmap
  22, on which every @{text Comp}-producing case here relies), rather
  than plain induction on the derivation of @{text "U \<Rightarrow>par V"}: the
  latter only ever gives an induction hypothesis for a rule's own
  \<^emph>\<open>immediate\<close> premises, which is not enough for the @{text ParApp} case
  when @{term U} is headed by an application whose function part is
  itself @{text Lam}-, @{text "Comp(Lam..)"}-, or @{text Eps}-headed:
  there, the function part's own components (@{text U3}, and @{text U4}
  for the @{text "Comp(Lam..)"} shape) are exposed by inverting the
  function part's own @{text "\<Rightarrow>par"}-step (safe, since that step's
  \<^emph>\<open>source\<close> shape is syntactically known and every rule's source pattern
  is headed by a distinct constructor), and strong induction is then
  applied to those strictly smaller components directly, rather than
  trying to invert an induction hypothesis whose target is a
  @{text sigma_nf}-wrapped, and hence not syntactically transparent,
  term.
\<close>

theorem par_step_triangle:
  assumes "is_sigma_normal U" and "U \<Rightarrow>par V"
  shows "V \<Rightarrow>par cd U"
  using assms
proof (induction "length_enve U" arbitrary: U V rule: less_induct)
  case less
  note nU = less.prems(1) and stepU = less.prems(2)
  from nU show ?case
  proof (cases rule: is_sigma_normal.cases)
    case NF_Id
    then show ?thesis using stepU by (auto elim: par_step.cases simp: par_step.ParId)
  next
    case (NF_Var x)
    then show ?thesis using stepU by (auto elim: par_step.cases simp: par_step.ParVar)
  next
    case (NF_Lam U1 x)
    obtain V1 where stepV1: "U1 \<Rightarrow>par V1" and Veq: "V = Lam x V1"
      using stepU unfolding NF_Lam by (auto elim: par_step.cases)
    have lt: "length_enve U1 < length_enve U" unfolding NF_Lam by simp
    have nU1: "is_sigma_normal U1" using NF_Lam by (auto elim: is_sigma_normal.cases)
    have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt nU1 stepV1] .
    show ?thesis unfolding Veq NF_Lam using IH1 by (simp add: par_step.ParLam)
  next
    case (NF_Eps U1)
    obtain V1 where stepV1: "U1 \<Rightarrow>par V1" and Veq: "V = Eps V1"
      using stepU unfolding NF_Eps by (auto elim: par_step.cases)
    have lt: "length_enve U1 < length_enve U" unfolding NF_Eps by simp
    have nU1: "is_sigma_normal U1" using NF_Eps by (auto elim: is_sigma_normal.cases)
    have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt nU1 stepV1] .
    show ?thesis unfolding Veq NF_Eps using IH1 by (simp add: par_step.ParEps)
  next
    case (NF_Ext U1 U2 x)
    obtain V1 V2 where stepV1: "U1 \<Rightarrow>par V1" and stepV2: "U2 \<Rightarrow>par V2"
        and Veq: "V = Ext V1 x V2"
      using stepU unfolding NF_Ext by (auto elim: par_step.cases)
    have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
      using NF_Ext by (auto elim: is_sigma_normal.cases)
    have lt1: "length_enve U1 < length_enve U" and lt2: "length_enve U2 < length_enve U"
      using length_pos [of U1] length_pos [of U2] unfolding NF_Ext by simp_all
    have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
    have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
    show ?thesis unfolding Veq NF_Ext using IH1 IH2 by (simp add: par_step.ParExtn)
  next
    case (NF_CompVar U1 x)
    obtain V1 where stepV1: "U1 \<Rightarrow>par V1" and Veq: "V = sigma_nf (Comp (Var x) V1)"
      using stepU unfolding NF_CompVar by (auto elim: par_step.cases)
    have nU1: "is_sigma_normal U1" using NF_CompVar by (auto elim: is_sigma_normal.cases)
    have lt1: "length_enve U1 < length_enve U"
      using length_pos [of U1] unfolding NF_CompVar by simp
    have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
    have nV1: "is_sigma_normal V1" using stepV1 by (rule par_step_target_normal)
    have "sigma_nf (Comp (Var x) V1) \<Rightarrow>par sigma_nf (Comp (Var x) (cd U1))"
      using is_sigma_normal.NF_Var nV1 par_step.ParVar IH1
      by (rule par_step_composition_compatibility)
    then show ?thesis unfolding Veq NF_CompVar by simp
  next
    case (NF_CompLam U1 U2 x)
    obtain V1 V2 where stepV1: "U1 \<Rightarrow>par V1" and stepV2: "U2 \<Rightarrow>par V2"
        and Veq: "V = sigma_nf (Comp (Lam x V1) V2)"
      using stepU unfolding NF_CompLam by (auto elim: par_step.cases)
    have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
      using NF_CompLam by (auto elim: is_sigma_normal.cases)
    have lt1: "length_enve U1 < length_enve U"
      using length_pos [of U1] length_pos [of U2] unfolding NF_CompLam by (simp add: algebra_simps)
    have lt2: "length_enve U2 < length_enve U"
    proof -
      have "(1::nat) \<le> 2 * length_enve U1" using length_pos [of U1] by linarith
      then have "1 * (length_enve U2 + 1) \<le> (2 * length_enve U1) * (length_enve U2 + 1)"
        by (rule mult_right_mono) simp
      then show ?thesis unfolding NF_CompLam by (simp add: algebra_simps)
    qed
    have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
    have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
    have nV1: "is_sigma_normal V1" using stepV1 by (rule par_step_target_normal)
    have nV2: "is_sigma_normal V2" using stepV2 by (rule par_step_target_normal)
    have step1: "Lam x V1 \<Rightarrow>par Lam x (cd U1)" using IH1 by (rule par_step.ParLam)
    have "sigma_nf (Comp (Lam x V1) V2) \<Rightarrow>par sigma_nf (Comp (Lam x (cd U1)) (cd U2))"
      using is_sigma_normal.NF_Lam [OF nV1] nV2 step1 IH2
      by (rule par_step_composition_compatibility)
    then show ?thesis unfolding Veq NF_CompLam by simp
  next
    case (NF_App U1 U2)
    have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
      using NF_App by (auto elim: is_sigma_normal.cases)
    have lt2: "length_enve U2 < length_enve U"
      using length_pos [of U1] length_pos [of U2] unfolding NF_App by simp
    note outerAppEq = NF_App
    from stepU [unfolded NF_App] show ?thesis
    proof (cases rule: par_step.cases)
      case (ParApp V1 V2)
      \<comment> \<open>@{term "U1 \<Rightarrow>par V1"}, @{term "U2 \<Rightarrow>par V2"}, @{term "V = App V1 V2"}.
          Case-split on the shape of @{term U1} to match @{text cd}'s own
          case split for @{term "App U1 U2"}; the three special shapes
          re-derive @{term V1}'s components by inverting
          @{text "stepV1"} itself (safe: its source, @{term U1}, has a
          syntactically known shape), then apply strong induction to
          those strictly smaller components directly.\<close>
      have stepV1: "U1 \<Rightarrow>par V1" and stepV2: "U2 \<Rightarrow>par V2" and stepVeq: "V = App V1 V2"
        using ParApp by simp_all
      have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
      from nU1 have "App V1 V2 \<Rightarrow>par cd (App U1 U2)"
      proof (cases rule: is_sigma_normal.cases)
        case (NF_Lam U3 x)
        obtain V3 where stepV3: "U3 \<Rightarrow>par V3" and V1eq: "V1 = Lam x V3"
          using stepV1 unfolding NF_Lam by (auto elim: par_step.cases)
        have lt3: "length_enve U3 < length_enve U"
          using length_pos [of U2] unfolding NF_App NF_Lam by simp
        have nU3: "is_sigma_normal U3" using NF_Lam by (auto elim: is_sigma_normal.cases)
        have IH3: "V3 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV3] .
        show ?thesis unfolding V1eq NF_Lam using IH3 IH2 by (simp add: par_step.ParBeta)
      next
        case (NF_CompLam U3 U4 x)
        obtain V3 V4 where stepV3: "U3 \<Rightarrow>par V3" and stepV4: "U4 \<Rightarrow>par V4"
            and V1eq: "V1 = sigma_nf (Comp (Lam x V3) V4)"
          using stepV1 unfolding NF_CompLam by (auto elim: par_step.cases)
        have neqU4: "U4 \<noteq> Id" using NF_CompLam by (auto elim: is_sigma_normal.cases)
        have lt3: "length_enve U3 < length_enve U"
          using length_pos [of U2] length_pos [of U3] length_pos [of U4]
          unfolding NF_App NF_CompLam by (simp add: algebra_simps)
        have lt4: "length_enve U4 < length_enve U"
        proof -
          have "(1::nat) \<le> 2 * length_enve U3" using length_pos [of U3] by linarith
          then have "1 * (length_enve U4 + 1) \<le> (2 * length_enve U3) * (length_enve U4 + 1)"
            by (rule mult_right_mono) simp
          then show ?thesis
            using length_pos [of U2] unfolding NF_App NF_CompLam by (simp add: algebra_simps)
        qed
        have nU3: "is_sigma_normal U3" and nU4: "is_sigma_normal U4"
          using NF_CompLam by (auto elim: is_sigma_normal.cases)
        have IH3: "V3 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV3] .
        have IH4: "V4 \<Rightarrow>par cd U4" using less.hyps [OF lt4 nU4 stepV4] .
        have nV3: "is_sigma_normal V3" using stepV3 by (rule par_step_target_normal)
        have nV4: "is_sigma_normal V4" using stepV4 by (rule par_step_target_normal)
        have main: "App V1 V2 \<Rightarrow>par sigma_nf (Comp (cd U3) (Ext (cd U2) x (cd U4)))"
        proof (cases "V4 = Id")
          case False
          have eq1: "sigma_nf (Comp (Lam x V3) V4) = Comp (Lam x V3) V4"
            using False by (intro sigma_nf_of_normal is_sigma_normal.NF_CompLam nV3 nV4)
          show ?thesis
            unfolding V1eq eq1 using par_step.ParBetaClos [OF IH3 IH2 IH4 False] .
        next
          case True
          have cdU4eq: "cd U4 = Id" using IH4 unfolding True by (auto elim: par_step.cases)
          have eq2: "sigma_nf (Comp (Lam x V3) V4) = Lam x V3"
            using True by (simp add: sigma_nf_Comp_IdR sigma_nf_of_normal [OF is_sigma_normal.NF_Lam [OF nV3]])
          show ?thesis
            unfolding V1eq eq2 cdU4eq using par_step.ParBeta [OF IH3 IH2] .
        qed
        show ?thesis unfolding V1eq NF_CompLam using main [unfolded V1eq] by simp
      next
        case (NF_Eps U3)
        obtain V3 where stepV3: "U3 \<Rightarrow>par V3" and V1eq: "V1 = Eps V3"
          using stepV1 unfolding NF_Eps by (auto elim: par_step.cases)
        have lt3: "length_enve U3 < length_enve U"
          using length_pos [of U2] unfolding NF_App NF_Eps by simp
        have nU3: "is_sigma_normal U3" using NF_Eps by (auto elim: is_sigma_normal.cases)
        have IH3: "V3 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV3] .
        show ?thesis unfolding V1eq NF_Eps using IH3 IH2 by (simp add: par_step.ParCompEps)
      next
        case NF_Id
        have lt1: "length_enve U1 < length_enve U"
          using length_pos [of U2] unfolding outerAppEq by simp
        have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
        show ?thesis using IH1 IH2 unfolding NF_Id by (simp add: par_step.ParApp)
      next
        case (NF_Var y)
        have lt1: "length_enve U1 < length_enve U"
          using length_pos [of U2] unfolding outerAppEq by simp
        have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
        show ?thesis using IH1 IH2 unfolding NF_Var by (simp add: par_step.ParApp)
      next
        case (NF_Ext U3 U4 x)
        have lt1: "length_enve U1 < length_enve U"
          using length_pos [of U2] unfolding outerAppEq by simp
        have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
        show ?thesis using IH1 IH2 unfolding NF_Ext by (simp add: par_step.ParApp)
      next
        case (NF_App U3 U4)
        note innerAppEq = NF_App
        have lt1: "length_enve U1 < length_enve U"
          using length_pos [of U2] unfolding outerAppEq by simp
        have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
        show ?thesis using IH1 IH2 unfolding innerAppEq by (simp add: par_step.ParApp)
      next
        case (NF_CompVar U3 x)
        have lt1: "length_enve U1 < length_enve U"
          using length_pos [of U2] unfolding outerAppEq by simp
        have IH1: "V1 \<Rightarrow>par cd U1" using less.hyps [OF lt1 nU1 stepV1] .
        show ?thesis using IH1 IH2 unfolding NF_CompVar by (simp add: par_step.ParApp)
      qed
      then show ?thesis unfolding stepVeq NF_App by simp
    next
      case ParBeta
      then obtain x U3 V1 V2 where
          U1eq: "U1 = Lam x U3" and
          stepV1: "U3 \<Rightarrow>par V1" and
          stepV2: "U2 \<Rightarrow>par V2" and
          stepVeq: "V = sigma_nf (Comp V1 (Ext V2 x Id))"
        by (auto simp: NF_App)
      have nU3: "is_sigma_normal U3" using nU1 unfolding U1eq
        by (auto elim: is_sigma_normal.cases)
      have lt3: "length_enve U3 < length_enve U"
        using length_pos [of U2] unfolding NF_App U1eq by simp
      have IH3: "V1 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV1] .
      have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
      have nV1: "is_sigma_normal V1" using stepV1 by (rule par_step_target_normal)
      have nV2: "is_sigma_normal V2" using stepV2 by (rule par_step_target_normal)
      have nExt: "is_sigma_normal (Ext V2 x Id)"
        using nV2 is_sigma_normal.NF_Id by (rule is_sigma_normal.NF_Ext)
      have stepExt: "Ext V2 x Id \<Rightarrow>par Ext (cd U2) x Id"
        using IH2 par_step.ParId by (rule par_step.ParExtn)
      have "sigma_nf (Comp V1 (Ext V2 x Id)) \<Rightarrow>par sigma_nf (Comp (cd U3) (Ext (cd U2) x Id))"
        using nV1 nExt IH3 stepExt by (rule par_step_composition_compatibility)
      then show ?thesis unfolding stepVeq U1eq NF_App by simp
    next
      case ParBetaClos
      then obtain x U3 U4 V1 V2 V3 where
          U1eq: "U1 = Comp (Lam x U3) U4" and
          stepV1: "U3 \<Rightarrow>par V1" and
          stepV2: "U2 \<Rightarrow>par V2" and
          stepV3: "U4 \<Rightarrow>par V3" and
          neq: "U4 \<noteq> Id" and
          stepVeq: "V = sigma_nf (Comp V1 (Ext V2 x V3))"
        by (auto simp: NF_App)
      have nU3: "is_sigma_normal U3" and nU4: "is_sigma_normal U4"
        using nU1 unfolding U1eq by (auto elim: is_sigma_normal.cases)
      have lt3: "length_enve U3 < length_enve U"
        using length_pos [of U2] length_pos [of U3] length_pos [of U4]
        unfolding NF_App U1eq by (simp add: algebra_simps)
      have lt4: "length_enve U4 < length_enve U"
      proof -
        have "(1::nat) \<le> 2 * length_enve U3" using length_pos [of U3] by linarith
        then have "1 * (length_enve U4 + 1) \<le> (2 * length_enve U3) * (length_enve U4 + 1)"
          by (rule mult_right_mono) simp
        then show ?thesis
          using length_pos [of U2] unfolding NF_App U1eq by (simp add: algebra_simps)
      qed
      have IH3: "V1 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV1] .
      have IH4: "V3 \<Rightarrow>par cd U4" using less.hyps [OF lt4 nU4 stepV3] .
      have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
      have nV1: "is_sigma_normal V1" using stepV1 by (rule par_step_target_normal)
      have nV2: "is_sigma_normal V2" using stepV2 by (rule par_step_target_normal)
      have nV3: "is_sigma_normal V3" using stepV3 by (rule par_step_target_normal)
      have nExt: "is_sigma_normal (Ext V2 x V3)"
        using nV2 nV3 by (rule is_sigma_normal.NF_Ext)
      have stepExt: "Ext V2 x V3 \<Rightarrow>par Ext (cd U2) x (cd U4)"
        using IH2 IH4 by (rule par_step.ParExtn)
      have "sigma_nf (Comp V1 (Ext V2 x V3)) \<Rightarrow>par sigma_nf (Comp (cd U3) (Ext (cd U2) x (cd U4)))"
        using nV1 nExt IH3 stepExt by (rule par_step_composition_compatibility)
      then show ?thesis unfolding stepVeq U1eq NF_App by simp
    next
      case ParCompEps
      then obtain U3 V1 V2 where
          U1eq: "U1 = Eps U3" and
          stepV1: "U3 \<Rightarrow>par V1" and
          stepV2: "U2 \<Rightarrow>par V2" and
          stepVeq: "V = sigma_nf (Comp V1 V2)"
        by (auto simp: NF_App)
      have nU3: "is_sigma_normal U3" using nU1 unfolding U1eq
        by (auto elim: is_sigma_normal.cases)
      have lt3: "length_enve U3 < length_enve U"
        using length_pos [of U2] unfolding NF_App U1eq by simp
      have IH3: "V1 \<Rightarrow>par cd U3" using less.hyps [OF lt3 nU3 stepV1] .
      have IH2: "V2 \<Rightarrow>par cd U2" using less.hyps [OF lt2 nU2 stepV2] .
      have nV1: "is_sigma_normal V1" using stepV1 by (rule par_step_target_normal)
      have nV2: "is_sigma_normal V2" using stepV2 by (rule par_step_target_normal)
      have "sigma_nf (Comp V1 V2) \<Rightarrow>par sigma_nf (Comp (cd U3) (cd U2))"
        using nV1 nV2 IH3 IH2 by (rule par_step_composition_compatibility)
      then show ?thesis unfolding stepVeq U1eq NF_App by simp
    qed
  qed
qed

end
