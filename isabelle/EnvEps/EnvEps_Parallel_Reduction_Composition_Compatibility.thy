theory EnvEps_Parallel_Reduction_Composition_Compatibility
  imports EnvEps_Parallel_Reduction_Reflexivity EnvEps_Sigma_Nf_Equiv
begin

text \<open>
  Composition compatibility of @{text "\<Rightarrow>par"} (docs file
  @{text "docs/enve-parallel-reduction-composition-compatibility.md"},
  thesis Lemma 7; roadmap item 22) -- the technical heart of the diamond
  property proof. Strong induction on @{text "length_enve (Comp U V)"}.
\<close>

theorem par_step_composition_compatibility:
  assumes "is_sigma_normal U" and "is_sigma_normal V"
    and "U \<Rightarrow>par U'" and "V \<Rightarrow>par V'"
  shows "sigma_nf (Comp U V) \<Rightarrow>par sigma_nf (Comp U' V')"
  using assms
proof (induction "length_enve (Comp U V)" arbitrary: U V U' V' rule: less_induct)
  case less
  note nU = less.prems(1) and nV = less.prems(2)
    and stepU = less.prems(3) and stepV = less.prems(4)
  show ?case
  proof (cases "V = Id")
    case True
    \<comment> \<open>Case 4.\<close>
    have "V' = Id" using stepV unfolding True by (auto elim: par_step.cases)
    with True have "sigma_nf (Comp U V) = U" "sigma_nf (Comp U' V') = U'"
      using nU par_step_target_normal [OF stepU] by (simp_all add: sigma_nf_Comp_IdR)
    then show ?thesis using stepU by simp
  next
    case Vok: False
    show ?thesis
    proof (cases "U = Id")
      case True
      \<comment> \<open>Case 3.\<close>
      have "U' = Id" using stepU unfolding True by (auto elim: par_step.cases)
      with True have "sigma_nf (Comp U V) = sigma_nf V" "sigma_nf (Comp U' V') = sigma_nf V'"
        by (simp_all add: sigma_nf_Comp_IdL)
      then show ?thesis using stepV nV par_step_target_normal [OF stepV] by simp
    next
      case Uni: False
      \<comment> \<open>@{term U} \<noteq> @{term Id}, @{term V} \<noteq> @{term Id}: case-split on @{term U}'s shape.\<close>
      from nU show ?thesis
      proof (cases rule: is_sigma_normal.cases)
        case NF_Id
        with Uni show ?thesis by simp
      next
        case (NF_Var x)
        \<comment> \<open>@{term U} = @{term "Var x"}: only @{text ParVar} matches, so @{term U'} = @{term U}.\<close>
        note Ueq = NF_Var
        have U'eq: "U' = Var x" using stepU unfolding Ueq by (auto elim: par_step.cases)
        from nV show ?thesis
        proof (cases rule: is_sigma_normal.cases)
          case NF_Id
          with Vok show ?thesis by simp
        next
          case (NF_Var y)
          \<comment> \<open>Case 2/1-symmetric "already normal": @{term V} = @{term "Var y"}. This is
              itself an "already normal" shape only in combination with @{term U};
              @{term "Comp U V"} is @{text Var}-headed composed with a further
              @{text Var} -- not one of the two @{text Comp}-shaped grammar
              productions, so it is \<^emph>\<open>not\<close> already normal in general (no rule of
              @{text "\<rightarrow>\<sigma>"} applies to @{term "Comp (Var x) (Var y)"} either, since
              none of the eight base rules' left-hand sides match a bare variable) --
              it is, in fact, already @{text "\<sigma>"}-irreducible via @{text NF_CompVar}
              (a variable is not an environment extension).\<close>
          note Veq = NF_Var
          have V'eq: "V' = Var y" using stepV unfolding Veq by (auto elim: par_step.cases)
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq Veq
            by (intro is_sigma_normal.NF_CompVar is_sigma_normal.NF_Var) simp_all
          have n2: "is_sigma_normal (Comp U' V')"
            unfolding U'eq V'eq
            by (intro is_sigma_normal.NF_CompVar is_sigma_normal.NF_Var) simp_all
          have e1: "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          have e2: "sigma_nf (Comp U' V') = Comp U' V'" using n2 by (rule sigma_nf_of_normal)
          have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV by (rule par_step.ParVarComp) (simp_all add: Veq U'eq)
          with e1 show ?thesis by simp
        next
          case (NF_Lam V1 y)
          \<comment> \<open>@{term V} = @{term "Lam y V1"}: already normal.\<close>
          note Veq = NF_Lam
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq using nV by (intro is_sigma_normal.NF_CompVar) (simp_all add: Vok Veq)
          have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV
            by (rule par_step.ParVarComp) (simp_all add: Vok Veq)
          ultimately show ?thesis by simp
        next
          case (NF_App V1 V2)
          note Veq = NF_App
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq using nV by (intro is_sigma_normal.NF_CompVar) (simp_all add: Vok Veq)
          have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV
            by (rule par_step.ParVarComp) (simp_all add: Vok Veq)
          ultimately show ?thesis by simp
        next
          case (NF_Eps V1)
          note Veq = NF_Eps
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq using nV by (intro is_sigma_normal.NF_CompVar) (simp_all add: Vok Veq)
          have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV
            by (rule par_step.ParVarComp) (simp_all add: Vok Veq)
          ultimately show ?thesis by simp
        next
          case (NF_CompLam V1 V3 y)
          note Veq = NF_CompLam
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq using nV by (intro is_sigma_normal.NF_CompVar) (simp_all add: Vok Veq)
          have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV
            by (rule par_step.ParVarComp) (simp_all add: Vok Veq)
          ultimately show ?thesis by simp
        next
          case (NF_CompVar V1 y)
          note Veq = NF_CompVar
          have n1: "is_sigma_normal (Comp U V)"
            unfolding Ueq using nV by (intro is_sigma_normal.NF_CompVar) (simp_all add: Vok Veq)
          have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
          moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
            unfolding Ueq U'eq using stepV
            by (rule par_step.ParVarComp) (simp_all add: Vok Veq)
          ultimately show ?thesis by simp
        next
          case (NF_Ext V1 V2 y)
          \<comment> \<open>Cases 6/7: @{term V} = @{term "Ext V1 y V2"}.\<close>
          note Veq = NF_Ext
          obtain V1' V2' where stepV1: "V1 \<Rightarrow>par V1'" and stepV2: "V2 \<Rightarrow>par V2'"
              and V'eq: "V' = Ext V1' y V2'"
            using stepV unfolding Veq by (auto elim: par_step.cases)
          show ?thesis
          proof (cases "x = y")
            case True
            \<comment> \<open>Case 6: @{text VarRef}.\<close>
            have "sigma_nf (Comp U V) = sigma_nf V1"
              unfolding Ueq Veq True by (rule sigma_nf_Comp_VarRef)
            moreover have "sigma_nf (Comp U' V') = sigma_nf V1'"
              unfolding U'eq V'eq True by (rule sigma_nf_Comp_VarRef)
            moreover have "is_sigma_normal V1" using nV unfolding Veq
              by (auto elim: is_sigma_normal.cases)
            moreover have "is_sigma_normal V1'" using stepV1 by (rule par_step_target_normal)
            ultimately show ?thesis using stepV1 by simp
          next
            case False
            \<comment> \<open>Case 7: @{text VarSkip}. Recurse via the induction hypothesis on the
                strictly shorter pair @{term "(U, V2)"}, since @{term V2} is a proper
                subterm of @{term V}.\<close>
            have "sigma_nf (Comp U V) = sigma_nf (Comp U V2)"
              unfolding Ueq Veq by (rule sigma_nf_Comp_VarSkip [OF False])
            moreover have "sigma_nf (Comp U' V') = sigma_nf (Comp U' V2')"
              unfolding U'eq V'eq by (rule sigma_nf_Comp_VarSkip [OF False])
            moreover have "is_sigma_normal V2" using nV unfolding Veq
              by (auto elim: is_sigma_normal.cases)
            moreover have lt: "length_enve (Comp U V2) < length_enve (Comp U V)"
              using length_pos [of V1] unfolding Veq Ueq by simp
            ultimately show ?thesis
              using less.hyps [OF lt _ _ stepU stepV2] nU stepU
              by simp
          qed
        qed
      next
        case (NF_Lam U1 x)
        \<comment> \<open>@{term U} = @{term "Lam x U1"}, @{term V} \<noteq> @{term Id}: already normal.\<close>
        note Ueq = NF_Lam
        obtain U1' where U1step: "U1 \<Rightarrow>par U1'" and U'eq: "U' = Lam x U1'"
          using stepU unfolding Ueq by (auto elim: par_step.cases)
        have nU1: "is_sigma_normal U1" using nU unfolding Ueq
          by (auto elim: is_sigma_normal.cases)
        have n1: "is_sigma_normal (Comp U V)"
          unfolding Ueq using nU1 nV by (intro is_sigma_normal.NF_CompLam) (simp_all add: Vok)
        have "sigma_nf (Comp U V) = Comp U V" using n1 by (rule sigma_nf_of_normal)
        moreover have "Comp U V \<Rightarrow>par sigma_nf (Comp U' V')"
          unfolding Ueq U'eq using U1step stepV Vok by (rule par_step.ParLamComp)
        ultimately show ?thesis by simp
      next
        case (NF_Ext U1 U2 x)
        \<comment> \<open>Case 5.\<close>
        note Ueq = NF_Ext
        obtain U1' U2' where stepU1: "U1 \<Rightarrow>par U1'" and stepU2: "U2 \<Rightarrow>par U2'"
            and U'eq: "U' = Ext U1' x U2'"
          using stepU unfolding Ueq by (auto elim: par_step.cases)
        have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
          using nU unfolding Ueq by (auto elim: is_sigma_normal.cases)
        have lt1: "length_enve (Comp U1 V) < length_enve (Comp U V)"
          by (rule length_enve_Comp_mono) (simp add: Ueq)
        have lt2: "length_enve (Comp U2 V) < length_enve (Comp U V)"
          by (rule length_enve_Comp_mono) (simp add: Ueq)
        have IH1: "sigma_nf (Comp U1 V) \<Rightarrow>par sigma_nf (Comp U1' V')"
          using less.hyps [OF lt1 nU1 nV stepU1 stepV] .
        have IH2: "sigma_nf (Comp U2 V) \<Rightarrow>par sigma_nf (Comp U2' V')"
          using less.hyps [OF lt2 nU2 nV stepU2 stepV] .
        have "sigma_nf (Comp U V) = Ext (sigma_nf (Comp U1 V)) x (sigma_nf (Comp U2 V))"
          unfolding Ueq by (rule sigma_nf_Comp_Ext)
        moreover have "sigma_nf (Comp U' V') = Ext (sigma_nf (Comp U1' V')) x (sigma_nf (Comp U2' V'))"
          unfolding U'eq by (rule sigma_nf_Comp_Ext)
        ultimately show ?thesis using IH1 IH2 by (simp add: par_step.ParExtn)
      next
        case (NF_Eps U1)
        \<comment> \<open>Case 9.\<close>
        note Ueq = NF_Eps
        obtain U1' where stepU1: "U1 \<Rightarrow>par U1'" and U'eq: "U' = Eps U1'"
          using stepU unfolding Ueq by (auto elim: par_step.cases)
        have nU1: "is_sigma_normal U1" using nU unfolding Ueq
          by (auto elim: is_sigma_normal.cases)
        have nU1': "is_sigma_normal U1'" using stepU1 by (rule par_step_target_normal)
        have "sigma_nf (Comp U V) = Eps U1"
          unfolding Ueq by (simp add: sigma_nf_Comp_Eps sigma_nf_of_normal [OF nU1])
        moreover have "sigma_nf (Comp U' V') = Eps U1'"
          unfolding U'eq by (simp add: sigma_nf_Comp_Eps sigma_nf_of_normal [OF nU1'])
        ultimately show ?thesis using stepU1 by (simp add: par_step.ParEps)
      next
        case (NF_CompLam U1 U2 x)
        \<comment> \<open>Case 1: @{term U} = @{term "Comp (Lam x U1) U2"}.\<close>
        note Ueq = NF_CompLam
        obtain U1' U2' where stepU1: "U1 \<Rightarrow>par U1'" and stepU2: "U2 \<Rightarrow>par U2'" and neqU2: "U2 \<noteq> Id"
            and U'eq: "U' = sigma_nf (Comp (Lam x U1') U2')"
          using stepU unfolding Ueq by (auto elim: par_step.cases)
        have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
          using nU unfolding Ueq by (auto elim: is_sigma_normal.cases)
        have lt2: "length_enve (Comp U2 V) < length_enve (Comp U V)"
        proof (rule length_enve_Comp_mono)
          have "(1::nat) \<le> 2 * length_enve U1" using length_pos [of U1] by linarith
          then have "1 * (length_enve U2 + 1) \<le> (2 * length_enve U1) * (length_enve U2 + 1)"
            by (rule mult_right_mono) simp
          then show "length_enve U2 < length_enve U"
            unfolding Ueq by (simp add: algebra_simps)
        qed
        have IH2: "sigma_nf (Comp U2 V) \<Rightarrow>par sigma_nf (Comp U2' V')"
          using less.hyps [OF lt2 nU2 nV stepU2 stepV] .
        have nLam: "is_sigma_normal (Lam x U1)" using nU1 by (rule is_sigma_normal.NF_Lam)
        have stepLam: "Lam x U1 \<Rightarrow>par Lam x U1'" using stepU1 by (rule par_step.ParLam)
        have lenW: "length_enve (sigma_nf (Comp U2 V)) \<le> length_enve (Comp U2 V)"
          by (rule length_enve_sigma_nf_le)
        have lt1: "length_enve (Comp (Lam x U1) (sigma_nf (Comp U2 V))) < length_enve (Comp U V)"
        proof -
          have step1: "length_enve (Comp (Lam x U1) (sigma_nf (Comp U2 V)))
                         \<le> 2 * length_enve U1 * (length_enve U2 * (length_enve V + 1) + 1)"
          proof -
            have "length_enve (sigma_nf (Comp U2 V)) + 1 \<le> length_enve U2 * (length_enve V + 1) + 1"
              using lenW by simp
            then have "length_enve U1 * (2 * (length_enve (sigma_nf (Comp U2 V)) + 1))
                         \<le> length_enve U1 * (2 * (length_enve U2 * (length_enve V + 1) + 1))"
              by (intro mult_le_mono2 mult_le_mono1) simp
            then show ?thesis by (simp add: algebra_simps)
          qed
          have step2: "2 * length_enve U1 * (length_enve U2 * (length_enve V + 1) + 1)
                         < 2 * length_enve U1 * (length_enve U2 * (length_enve V + 1) + (length_enve V + 1))"
            using length_pos [of U1] length_pos [of V]
            by (intro mult_less_mono2) simp_all
          have step3: "2 * length_enve U1 * (length_enve U2 * (length_enve V + 1) + (length_enve V + 1))
                         = length_enve (Comp U V)"
            unfolding Ueq by (simp add: algebra_simps)
          from step1 step2 step3 show ?thesis by linarith
        qed
        have IH1: "sigma_nf (Comp (Lam x U1) (sigma_nf (Comp U2 V)))
                     \<Rightarrow>par sigma_nf (Comp (Lam x U1') (sigma_nf (Comp U2' V')))"
          using less.hyps [OF lt1 nLam is_sigma_normal_sigma_nf [of "Comp U2 V"] stepLam IH2] .
        have "sigma_nf (Comp U V) = sigma_nf (Comp (Lam x U1) (Comp U2 V))"
          unfolding Ueq by (rule sigma_nf_Comp_Assoc)
        also have "\<dots> = sigma_nf (Comp (Lam x U1) (sigma_nf (Comp U2 V)))"
          by (rule sigma_nf_Comp_idem_R)
        finally have lhs: "sigma_nf (Comp U V)
            = sigma_nf (Comp (Lam x U1) (sigma_nf (Comp U2 V)))" .
        have "sigma_nf (Comp U' V') = sigma_nf (Comp (Comp (Lam x U1') U2') V')"
          unfolding U'eq by (rule sigma_nf_Comp_idem_L [symmetric])
        also have "\<dots> = sigma_nf (Comp (Lam x U1') (Comp U2' V'))"
          by (rule sigma_nf_Comp_Assoc)
        also have "\<dots> = sigma_nf (Comp (Lam x U1') (sigma_nf (Comp U2' V')))"
          by (rule sigma_nf_Comp_idem_R)
        finally have rhs: "sigma_nf (Comp U' V')
            = sigma_nf (Comp (Lam x U1') (sigma_nf (Comp U2' V')))" .
        show ?thesis unfolding lhs rhs using IH1 .
      next
        case (NF_CompVar U1 x)
        \<comment> \<open>Case 2: @{term U} = @{term "Comp (Var x) U1"}.\<close>
        note Ueq = NF_CompVar
        obtain U1' where stepU1: "U1 \<Rightarrow>par U1'" and neqU1: "U1 \<noteq> Id"
            and notextU1: "\<nexists>P y Q. U1 = Ext P y Q"
            and U'eq: "U' = sigma_nf (Comp (Var x) U1')"
          using stepU unfolding Ueq by (auto elim: par_step.cases)
        have nU1: "is_sigma_normal U1" using nU unfolding Ueq
          by (auto elim: is_sigma_normal.cases)
        have lt1: "length_enve (Comp U1 V) < length_enve (Comp U V)"
          by (rule length_enve_Comp_mono) (simp add: Ueq)
        have IH1: "sigma_nf (Comp U1 V) \<Rightarrow>par sigma_nf (Comp U1' V')"
          using less.hyps [OF lt1 nU1 nV stepU1 stepV] .
        have "sigma_nf (Comp U V) = sigma_nf (Comp (Var x) (Comp U1 V))"
          unfolding Ueq by (rule sigma_nf_Comp_Assoc)
        also have "\<dots> = sigma_nf (Comp (Var x) (sigma_nf (Comp U1 V)))"
          by (rule sigma_nf_Comp_idem_R)
        finally have lhs: "sigma_nf (Comp U V)
            = sigma_nf (Comp (Var x) (sigma_nf (Comp U1 V)))" .
        have "sigma_nf (Comp U' V') = sigma_nf (Comp (Comp (Var x) U1') V')"
          unfolding U'eq by (rule sigma_nf_Comp_idem_L [symmetric])
        also have "\<dots> = sigma_nf (Comp (Var x) (Comp U1' V'))"
          by (rule sigma_nf_Comp_Assoc)
        also have "\<dots> = sigma_nf (Comp (Var x) (sigma_nf (Comp U1' V')))"
          by (rule sigma_nf_Comp_idem_R)
        finally have rhs: "sigma_nf (Comp U' V')
            = sigma_nf (Comp (Var x) (sigma_nf (Comp U1' V')))" .
        \<comment> \<open>@{term "Comp (Var x) (sigma_nf (Comp U1 V))"} need not itself be
            @{text "\<sigma>"}-normal (the inner @{text sigma_nf} could collapse to
            @{term Id} or an environment extension), so the target is reached
            not by a single direct @{text ParVarComp} application but by
            recursing the whole lemma once more, on the strictly shorter pair
            @{term "(Var x, sigma_nf (Comp U1 V))"}.\<close>
        have lt2: "length_enve (Comp (Var x) (sigma_nf (Comp U1 V))) < length_enve (Comp U V)"
        proof -
          have "length_enve (sigma_nf (Comp U1 V)) \<le> length_enve (Comp U1 V)"
            by (rule length_enve_sigma_nf_le)
          then have "length_enve (Comp (Var x) (sigma_nf (Comp U1 V)))
                       \<le> length_enve U1 * length_enve V + length_enve U1 + 1"
            by (simp add: algebra_simps)
          also have "\<dots> < length_enve (Comp U V)"
            unfolding Ueq using length_pos [of V] by (simp add: algebra_simps)
          finally show ?thesis .
        qed
        have nVar: "is_sigma_normal (Var x)" by (rule is_sigma_normal.NF_Var)
        have stepVar: "Var x \<Rightarrow>par Var x" by (rule par_step.ParVar)
        have "sigma_nf (Comp (Var x) (sigma_nf (Comp U1 V)))
                \<Rightarrow>par sigma_nf (Comp (Var x) (sigma_nf (Comp U1' V')))"
          using less.hyps [OF lt2 nVar is_sigma_normal_sigma_nf [of "Comp U1 V"] stepVar IH1] .
        with lhs rhs show ?thesis by simp
      next
        case (NF_App U1 U2)
        \<comment> \<open>Case 8: @{term U} = @{term "App U1 U2"}. Sub-case on the rule
            deriving @{term "U \<Rightarrow>par U'"}.\<close>
        note Ueq = NF_App
        have nU1: "is_sigma_normal U1" and nU2: "is_sigma_normal U2"
          using nU unfolding Ueq by (auto elim: is_sigma_normal.cases)
        have lt2: "length_enve (Comp U2 V) < length_enve (Comp U V)"
          by (rule length_enve_Comp_mono) (simp add: Ueq)
        have IH2: "sigma_nf (Comp U2 V) \<Rightarrow>par sigma_nf (Comp U2' V')"
          if "U2 \<Rightarrow>par U2'" for U2'
          using less.hyps [OF lt2 nU2 nV that stepV] .
        from stepU [unfolded Ueq] show ?thesis
        proof (cases rule: par_step.cases)
          case (ParApp U1'' U2'')
          \<comment> \<open>Via @{text ParApp}.\<close>
          then have eqs: "U' = App U1'' U2''"
              and stepU1: "U1 \<Rightarrow>par U1''" and stepU2: "U2 \<Rightarrow>par U2''"
            by (auto simp: Ueq)
          have lt1: "length_enve (Comp U1 V) < length_enve (Comp U V)"
            by (rule length_enve_Comp_mono) (simp add: Ueq)
          have IH1: "sigma_nf (Comp U1 V) \<Rightarrow>par sigma_nf (Comp U1'' V')"
            using less.hyps [OF lt1 nU1 nV stepU1 stepV] .
          have "sigma_nf (Comp U V) = App (sigma_nf (Comp U1 V)) (sigma_nf (Comp U2 V))"
            unfolding Ueq by (rule sigma_nf_Comp_App)
          moreover have "sigma_nf (Comp U' V') = App (sigma_nf (Comp U1'' V')) (sigma_nf (Comp U2'' V'))"
            unfolding eqs by (rule sigma_nf_Comp_App)
          ultimately show ?thesis
            using IH1 IH2 [OF stepU2] by (simp add: par_step.ParApp)
        next
          case (ParBeta U3 U3'' U2'' x)
          \<comment> \<open>Via @{text ParBeta}: @{term U1} = @{term "Lam x U3"}. Since
              @{term V} \<noteq> @{term Id}, @{term "Comp U1 V"} is already
              @{text "\<sigma>"}-normal, so the whole term
              @{term "App (Comp U1 V) (sigma_nf (Comp U2 V))"} is exactly the
              @{text ParBetaClos} pattern with closure environment @{term V}
              itself; no separate @{text ParApp} step is needed.\<close>
          then have Ueq1: "U1 = Lam x U3"
              and stepU3: "U3 \<Rightarrow>par U3''" and stepU2': "U2 \<Rightarrow>par U2''"
              and U'eq: "U' = sigma_nf (Comp U3'' (Ext U2'' x Id))"
            by (auto simp: Ueq)
          have nU3: "is_sigma_normal U3" using nU1 unfolding Ueq1
            by (auto elim: is_sigma_normal.cases)
          have U1Vnormal: "sigma_nf (Comp U1 V) = Comp U1 V"
            using Vok unfolding Ueq1
            by (intro sigma_nf_of_normal is_sigma_normal.NF_CompLam nU3 nV)
          have lhs: "sigma_nf (Comp U V) = App (Comp U1 V) (sigma_nf (Comp U2 V))"
            unfolding Ueq by (simp add: sigma_nf_Comp_App U1Vnormal)
          have step: "App (Comp U1 V) (sigma_nf (Comp U2 V))
                        \<Rightarrow>par sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x V'))"
            unfolding Ueq1
            by (rule par_step.ParBetaClos [OF stepU3 IH2 [OF stepU2'] stepV Vok])
          have rhs: "sigma_nf (Comp U' V')
                       = sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x V'))"
          proof -
            have "sigma_nf (Comp U' V') = sigma_nf (Comp (Comp U3'' (Ext U2'' x Id)) V')"
              unfolding U'eq by (rule sigma_nf_Comp_idem_L [symmetric])
            also have "\<dots> = sigma_nf (Comp U3'' (Comp (Ext U2'' x Id) V'))"
              by (rule sigma_nf_Comp_Assoc)
            also have "\<dots> = sigma_nf (Comp U3'' (sigma_nf (Comp (Ext U2'' x Id) V')))"
              by (rule sigma_nf_Comp_idem_R)
            also have "\<dots> = sigma_nf (Comp U3''
                (Ext (sigma_nf (Comp U2'' V')) x (sigma_nf (Comp Id V'))))"
              by (simp only: sigma_nf_Comp_Ext)
            also have "\<dots> = sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x V'))"
              using par_step_target_normal [OF stepV]
              by (simp add: sigma_nf_Comp_IdL)
            finally show ?thesis .
          qed
          show ?thesis unfolding lhs rhs using step .
        next
          case (ParBetaClos U3 U3'' U2'' U4 U4'' x)
          \<comment> \<open>Via @{text ParBetaClos}: @{term U1} = @{term "Comp (Lam x U3) U4"}.
              Unlike @{text ParBeta}, whether @{term "Comp U1 V"} is already
              normal depends on whether @{term "sigma_nf (Comp U4 V)"} happens
              to equal @{term Id}; both possibilities are handled, landing on
              @{text ParBetaClos} or @{text ParBeta} respectively at the top
              level (never @{text ParApp}, for the same reason as the
              @{text ParBeta} sub-case above).\<close>
          then have Ueq1: "U1 = Comp (Lam x U3) U4"
              and stepU3: "U3 \<Rightarrow>par U3''" and stepU4: "U4 \<Rightarrow>par U4''"
              and stepU2': "U2 \<Rightarrow>par U2''" and neqU4: "U4 \<noteq> Id"
              and U'eq: "U' = sigma_nf (Comp U3'' (Ext U2'' x U4''))"
            by (auto simp: Ueq)
          have nU3: "is_sigma_normal U3" and nU4: "is_sigma_normal U4"
            using nU1 unfolding Ueq1 by (auto elim: is_sigma_normal.cases)
          have lt4: "length_enve (Comp U4 V) < length_enve (Comp U V)"
          proof (rule length_enve_Comp_mono)
            have "(1::nat) \<le> 2 * length_enve U3" using length_pos [of U3] by linarith
            then have "1 * (length_enve U4 + 1) \<le> (2 * length_enve U3) * (length_enve U4 + 1)"
              by (rule mult_right_mono) simp
            then show "length_enve U4 < length_enve U"
              unfolding Ueq Ueq1 by (simp add: algebra_simps)
          qed
          have IH4: "sigma_nf (Comp U4 V) \<Rightarrow>par sigma_nf (Comp U4'' V')"
            using less.hyps [OF lt4 nU4 nV stepU4 stepV] .
          have lt2: "length_enve (Comp U2 V) < length_enve (Comp U V)"
            by (rule length_enve_Comp_mono) (simp add: Ueq)
          have IH2': "sigma_nf (Comp U2 V) \<Rightarrow>par sigma_nf (Comp U2'' V')"
            using less.hyps [OF lt2 nU2 nV stepU2' stepV] .
          have U1Veq: "sigma_nf (Comp U1 V) = sigma_nf (Comp (Lam x U3) (sigma_nf (Comp U4 V)))"
          proof -
            have "sigma_nf (Comp U1 V) = sigma_nf (Comp (Lam x U3) (Comp U4 V))"
              unfolding Ueq1 by (rule sigma_nf_Comp_Assoc)
            also have "\<dots> = sigma_nf (Comp (Lam x U3) (sigma_nf (Comp U4 V)))"
              by (rule sigma_nf_Comp_idem_R)
            finally show ?thesis .
          qed
          have lhs: "sigma_nf (Comp U V)
              = App (sigma_nf (Comp U1 V)) (sigma_nf (Comp U2 V))"
            unfolding Ueq by (rule sigma_nf_Comp_App)
          have rhs: "sigma_nf (Comp U' V')
              = sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x (sigma_nf (Comp U4'' V'))))"
          proof -
            have "sigma_nf (Comp U' V') = sigma_nf (Comp (Comp U3'' (Ext U2'' x U4'')) V')"
              unfolding U'eq by (rule sigma_nf_Comp_idem_L [symmetric])
            also have "\<dots> = sigma_nf (Comp U3'' (Comp (Ext U2'' x U4'') V'))"
              by (rule sigma_nf_Comp_Assoc)
            also have "\<dots> = sigma_nf (Comp U3'' (sigma_nf (Comp (Ext U2'' x U4'') V')))"
              by (rule sigma_nf_Comp_idem_R)
            also have "\<dots> = sigma_nf (Comp U3''
                (Ext (sigma_nf (Comp U2'' V')) x (sigma_nf (Comp U4'' V'))))"
              by (simp only: sigma_nf_Comp_Ext)
            finally show ?thesis .
          qed
          show ?thesis
          proof (cases "sigma_nf (Comp U4 V) = Id")
            case False
            \<comment> \<open>@{term "Comp U1 V"} is already normal (@{text NF_CompLam}
                applied one level in): a @{text ParBetaClos} redex.\<close>
            have U1Vn: "sigma_nf (Comp U1 V) = Comp (Lam x U3) (sigma_nf (Comp U4 V))"
              unfolding U1Veq
              by (intro sigma_nf_of_normal is_sigma_normal.NF_CompLam nU3
                        is_sigma_normal_sigma_nf False)
            have "App (sigma_nf (Comp U1 V)) (sigma_nf (Comp U2 V))
                    \<Rightarrow>par sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x (sigma_nf (Comp U4'' V'))))"
              unfolding U1Vn
              by (rule par_step.ParBetaClos [OF stepU3 IH2' IH4 False])
            with lhs rhs show ?thesis by simp
          next
            case True
            \<comment> \<open>@{term "Comp U1 V"} collapses one level further, to
                @{term "Lam x U3"} alone: a @{text ParBeta} redex. Since
                @{text "\<Rightarrow>par"} only ever maps @{term Id} to @{term Id}, the
                image @{term "sigma_nf (Comp U4'' V')"} is forced to be
                @{term Id} too, matching @{text ParBeta}'s target shape.\<close>
            have U4''eq: "sigma_nf (Comp U4'' V') = Id"
              using IH4 unfolding True by (auto elim: par_step.cases)
            have U1Vn: "sigma_nf (Comp U1 V) = Lam x U3"
              unfolding U1Veq True
              by (simp add: sigma_nf_Comp_IdR sigma_nf_of_normal [OF is_sigma_normal.NF_Lam [OF nU3]])
            have "App (sigma_nf (Comp U1 V)) (sigma_nf (Comp U2 V))
                    \<Rightarrow>par sigma_nf (Comp U3'' (Ext (sigma_nf (Comp U2'' V')) x Id))"
              unfolding U1Vn by (rule par_step.ParBeta [OF stepU3 IH2'])
            with lhs rhs U4''eq show ?thesis by simp
          qed
        next
          case (ParCompEps U3 U3'' U2'')
          \<comment> \<open>Via @{text ParComp\<^sub>\<epsilon>}: @{term U1} = @{term "Eps U3"}. Since
              @{term "Comp (Eps U3) V"} always reduces (via @{text "Eps-eps"})
              directly to @{term "Eps U3"}, no case split on @{term V} is
              needed here.\<close>
          then have Ueq1: "U1 = Eps U3"
              and stepU3: "U3 \<Rightarrow>par U3''" and stepU2': "U2 \<Rightarrow>par U2''"
              and U'eq: "U' = sigma_nf (Comp U3'' U2'')"
            by (auto simp: Ueq)
          have lt2: "length_enve (Comp U2 V) < length_enve (Comp U V)"
            by (rule length_enve_Comp_mono) (simp add: Ueq)
          have IH2': "sigma_nf (Comp U2 V) \<Rightarrow>par sigma_nf (Comp U2'' V')"
            using less.hyps [OF lt2 nU2 nV stepU2' stepV] .
          have nU3: "is_sigma_normal U3" using nU1 unfolding Ueq1
            by (auto elim: is_sigma_normal.cases)
          have lhs: "sigma_nf (Comp U V) = App (Eps U3) (sigma_nf (Comp U2 V))"
            unfolding Ueq Ueq1
            by (simp add: sigma_nf_Comp_App sigma_nf_Comp_Eps sigma_nf_of_normal [OF nU3])
          have rhs: "sigma_nf (Comp U' V') = sigma_nf (Comp U3'' (sigma_nf (Comp U2'' V')))"
          proof -
            have "sigma_nf (Comp U' V') = sigma_nf (Comp (Comp U3'' U2'') V')"
              unfolding U'eq by (rule sigma_nf_Comp_idem_L [symmetric])
            also have "\<dots> = sigma_nf (Comp U3'' (Comp U2'' V'))"
              by (rule sigma_nf_Comp_Assoc)
            also have "\<dots> = sigma_nf (Comp U3'' (sigma_nf (Comp U2'' V')))"
              by (rule sigma_nf_Comp_idem_R)
            finally show ?thesis .
          qed
          have "App (Eps U3) (sigma_nf (Comp U2 V)) \<Rightarrow>par sigma_nf (Comp U3'' (sigma_nf (Comp U2'' V')))"
            by (rule par_step.ParCompEps [OF stepU3 IH2'])
          with lhs rhs show ?thesis by simp
        qed
      qed
    qed
  qed
qed

end
