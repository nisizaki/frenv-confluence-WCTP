theory EnvEps_Parallel_Reduction_Soundness
  imports EnvEps_Parallel_Reduction_Reflexivity EnvEps_Beta_Over_Sigma_Congruence
    EnvEps_Sigma_Nf_Equiv
begin

text \<open>
  Soundness of @{text "\<Rightarrow>par"} with respect to @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} (docs
  file @{text "docs/enve-parallel-reduction-soundness.md"}, thesis
  Theorem 9, presented there as a Lemma; roadmap item 20) -- the converse
  direction to @{text EnvEps_Parallel_Reduction_Simulation}. The docs'
  own "context monotonicity of @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"}" Fact (lifting through
  @{text Lam}, @{text Eps}, @{text App}, @{text Ext}, and @{text Comp}
  with a fixed @{text Lam}-/@{text Var}-headed partner) is formalized in
  @{text EnvEps_Beta_Over_Sigma_Congruence}, with the @{text Comp}-lifting
  lemmas wrapping their result in @{text sigma_nf} rather than carrying
  the docs' informal "shape preserved" side condition, so they hold
  unconditionally.

  Proof is by induction on the derivation of @{text "U \<Rightarrow>par U'"}.

  \<^bold>\<open>Fixed foundational mismatch (@{text ParBetaClos}).\<close> @{text
  EnvEps_BetaSigma}'s own @{text BetaClos} rule (roadmap item 15) now
  fires on the @{text Comp}-headed @{text "App (Comp (Lam x M) L) N"}
  shape, matching the thesis's own Definition 5 literally and, with it,
  the shape the @{text ParBetaClos} case needs once its three arguments
  have been lifted to their targets. The case is proved by lifting each
  argument in turn through @{text EnvEps_Beta_Over_Sigma_Congruence}'s
  @{text AppL}/@{text AppR}/@{text CompL_Lam}/@{text CompR_Lam} lemmas,
  then case-splitting on whether the lifted closure environment
  @{text "W'"} collapses to @{text Id} (landing on @{text
  beta_over_sigma_step_Beta}) or not (landing on the new @{text
  beta_over_sigma_step_BetaClos}, added alongside @{text
  beta_over_sigma_step_Beta}/@{text beta_over_sigma_step_CompEps}).

  \<^bold>\<open>Fixed remaining gap (@{text ParVarComp}).\<close> This case had a distinct,
  unrelated gap: lifting @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>\<^sup>*"} through a fixed @{text
  Var}-headed @{text Comp} partner needs every waypoint of the chain to
  stay clear of both @{text Id} and environment-extension shape
  (grammar's @{text NF_CompVar}) -- and unlike @{text Id} (which is a
  genuine dead end for @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}, roadmap's own @{text
  beta_over_sigma_step_not_from_Id}), becoming environment-extension-shaped
  mid-chain is not terminal, so the simple "only the last step can
  collapse" argument used for the @{text Lam}-headed case does not carry
  over. Resolved below via a dedicated well-founded induction on
  @{text "length_enve W"}: at each @{text "\<sigma>"}-step of @{text W}, either
  the step falls inside an @{text Ext}-shaped waypoint (handled via a new
  inversion lemma, @{text beta_over_sigma_step_Ext_inv}, splitting into
  the @{text VarRef} sub-case, where the change is either absorbed
  entirely -- when it hits the discarded sub-tree -- or transported
  directly; and the @{text VarSkip} sub-case, which recurses the whole
  argument on the strictly shorter environment tail) or it does not, in
  which case @{text "Comp (Var x) W"} is already @{text "\<sigma>"}-normal
  (grammar's @{text NF_CompVar}) and @{text beta_over_sigma_step_CompR}
  (fully general, no side condition) lifts it directly.
\<close>

lemma beta_step_Ext_inv:
  "Ext A x B \<rightarrow>\<beta> M \<Longrightarrow> (\<exists>A'. M = Ext A' x B \<and> A \<rightarrow>\<beta> A') \<or> (\<exists>B'. M = Ext A x B' \<and> B \<rightarrow>\<beta> B')"
  by (cases rule: EnvEps_Beta_Step.beta_step.cases) auto

lemma beta_over_sigma_step_Ext_inv:
  assumes step: "Ext A x B \<rightarrow>\<beta>\<bar>\<sigma> C" and nA: "is_sigma_normal A" and nB: "is_sigma_normal B"
  shows "(\<exists>A'. C = Ext A' x B \<and> A \<rightarrow>\<beta>\<bar>\<sigma> A') \<or> (\<exists>B'. C = Ext A x B' \<and> B \<rightarrow>\<beta>\<bar>\<sigma> B')"
proof -
  obtain M where M1: "Ext A x B \<rightarrow>\<beta> M" and M2: "M \<rightarrow>\<sigma>\<^sup>* C" and nC: "is_sigma_normal C"
    using step by (auto simp: beta_over_sigma_step_def)
  have Ceq: "sigma_nf M = C"
  proof (rule sigma_nf_eq_if_reduces_and_irreducible [OF M2])
    show "sigma_irreducible C" using nC by (simp add: sigma_normal_form_grammar)
  qed
  from beta_step_Ext_inv [OF M1]
  show ?thesis
  proof (elim disjE exE conjE)
    fix A' assume Meq: "M = Ext A' x B" and stepA: "A \<rightarrow>\<beta> A'"
    have "A \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf A'"
      using stepA sigma_nf_reduces is_sigma_normal_sigma_nf by (auto simp: beta_over_sigma_step_def)
    moreover have "C = Ext (sigma_nf A') x B"
      using Ceq [symmetric] unfolding Meq by (simp add: sigma_nf_Ext sigma_nf_of_normal [OF nB])
    ultimately show ?thesis by blast
  next
    fix B' assume Meq: "M = Ext A x B'" and stepB: "B \<rightarrow>\<beta> B'"
    have "B \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf B'"
      using stepB sigma_nf_reduces is_sigma_normal_sigma_nf by (auto simp: beta_over_sigma_step_def)
    moreover have "C = Ext A x (sigma_nf B')"
      using Ceq [symmetric] unfolding Meq by (simp add: sigma_nf_Ext sigma_nf_of_normal [OF nA])
    ultimately show ?thesis by blast
  qed
qed

lemma beta_over_sigma_step_CompR_Var:
  assumes stepW: "W \<rightarrow>\<beta>\<bar>\<sigma> W'" and nW: "is_sigma_normal W"
  shows "sigma_nf (Comp (Var x) W) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Var x) W')"
  using stepW nW
proof (induction "length_enve W" arbitrary: W W' rule: less_induct)
  case less
  note stepW = less.prems(1) and nW = less.prems(2)
  show ?case
  proof (cases "\<exists>P y Q. W = Ext P y Q")
    case True
    then obtain P y Q where Weq: "W = Ext P y Q" by blast
    have nP: "is_sigma_normal P" and nQ: "is_sigma_normal Q"
      using nW unfolding Weq by (auto elim: is_sigma_normal.cases)
    from beta_over_sigma_step_Ext_inv [OF stepW [unfolded Weq] nP nQ]
    show ?thesis
    proof (elim disjE exE conjE)
      fix P' assume W'eq: "W' = Ext P' y Q" and stepP: "P \<rightarrow>\<beta>\<bar>\<sigma> P'"
      have nP': "is_sigma_normal P'" using stepP by (rule beta_over_sigma_step_target_normal)
      show ?thesis
      proof (cases "y = x")
        case True
        have src: "sigma_nf (Comp (Var x) W) = sigma_nf P"
          unfolding Weq True by (rule sigma_nf_Comp_VarRef)
        have tgt: "sigma_nf (Comp (Var x) W') = sigma_nf P'"
          unfolding W'eq True by (rule sigma_nf_Comp_VarRef)
        show ?thesis
          unfolding src tgt sigma_nf_of_normal [OF nP] sigma_nf_of_normal [OF nP']
          using stepP by (rule r_into_rtranclp)
      next
        case False
        have src: "sigma_nf (Comp (Var x) W) = sigma_nf (Comp (Var x) Q)"
          unfolding Weq using False [symmetric] by (rule sigma_nf_Comp_VarSkip)
        have tgt: "sigma_nf (Comp (Var x) W') = sigma_nf (Comp (Var x) Q)"
          unfolding W'eq using False [symmetric] by (rule sigma_nf_Comp_VarSkip)
        show ?thesis unfolding src tgt by (rule rtranclp.rtrancl_refl)
      qed
    next
      fix Q' assume W'eq: "W' = Ext P y Q'" and stepQ: "Q \<rightarrow>\<beta>\<bar>\<sigma> Q'"
      show ?thesis
      proof (cases "y = x")
        case True
        have src: "sigma_nf (Comp (Var x) W) = sigma_nf P"
          unfolding Weq True by (rule sigma_nf_Comp_VarRef)
        have tgt: "sigma_nf (Comp (Var x) W') = sigma_nf P"
          unfolding W'eq True by (rule sigma_nf_Comp_VarRef)
        show ?thesis unfolding src tgt by (rule rtranclp.rtrancl_refl)
      next
        case False
        have src: "sigma_nf (Comp (Var x) W) = sigma_nf (Comp (Var x) Q)"
          unfolding Weq using False [symmetric] by (rule sigma_nf_Comp_VarSkip)
        have tgt: "sigma_nf (Comp (Var x) W') = sigma_nf (Comp (Var x) Q')"
          unfolding W'eq using False [symmetric] by (rule sigma_nf_Comp_VarSkip)
        have lt: "length_enve Q < length_enve W" unfolding Weq by simp
        have "sigma_nf (Comp (Var x) Q) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Var x) Q')"
          using less.hyps [OF lt stepQ nQ] .
        then show ?thesis unfolding src tgt .
      qed
    qed
  next
    case False
    note notExt = False
    show ?thesis
    proof (cases "W = Id")
      case True
      show ?thesis using stepW [unfolded True] beta_over_sigma_step_not_from_Id by blast
    next
      case False
      have nVarX: "is_sigma_normal (Var x)" by (rule is_sigma_normal.NF_Var)
      have nComp: "is_sigma_normal (Comp (Var x) W)"
        by (intro is_sigma_normal.NF_CompVar nW False notExt)
      have src: "sigma_nf (Comp (Var x) W) = Comp (Var x) W"
        using nComp by (rule sigma_nf_of_normal)
      have "Comp (Var x) W \<rightarrow>\<beta>\<bar>\<sigma> sigma_nf (Comp (Var x) W')"
        using stepW nVarX by (rule beta_over_sigma_step_CompR)
      then show ?thesis unfolding src by (rule r_into_rtranclp)
    qed
  qed
qed

lemma beta_over_sigma_steps_CompR_Var:
  assumes chain: "W \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* W'" and nW: "is_sigma_normal W"
  shows "sigma_nf (Comp (Var x) W) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Var x) W')"
  using chain
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step y z)
  have ny: "is_sigma_normal y" using nW step.hyps(1) by (rule beta_over_sigma_steps_target_normal)
  have "sigma_nf (Comp (Var x) y) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Var x) z)"
    using step.hyps(2) ny by (rule beta_over_sigma_step_CompR_Var)
  with step.IH show ?case by (rule rtranclp_trans)
qed

theorem par_step_sound_for_beta_over_sigma:
  assumes "is_sigma_normal U" and "U \<Rightarrow>par U'"
  shows "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* U'"
  using assms(2)
proof (induction rule: par_step.induct)
  case (ParVar x)
  show ?case by simp
next
  case ParId
  show ?case by simp
next
  case (ParLam U U' x)
  then show ?case using beta_over_sigma_steps_Lam by simp
next
  case (ParEps U U')
  then show ?case using beta_over_sigma_steps_Eps by simp
next
  case (ParApp U U' V V')
  have nV: "is_sigma_normal V" using ParApp.hyps(2) by (rule par_step_source_normal)
  have nU': "is_sigma_normal U'" using ParApp.hyps(1) by (rule par_step_target_normal)
  have "App U V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App U' V"
    using ParApp.IH(1) nV by (rule beta_over_sigma_steps_AppL)
  also have "App U' V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App U' V'"
    using ParApp.IH(2) nU' by (rule beta_over_sigma_steps_AppR)
  finally show ?case .
next
  case (ParExtn U U' V V' x)
  have nV: "is_sigma_normal V" using ParExtn.hyps(2) by (rule par_step_source_normal)
  have nU': "is_sigma_normal U'" using ParExtn.hyps(1) by (rule par_step_target_normal)
  have "Ext U x V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext U' x V"
    using ParExtn.IH(1) nV by (rule beta_over_sigma_steps_ExtnL)
  also have "Ext U' x V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Ext U' x V'"
    using ParExtn.IH(2) nU' by (rule beta_over_sigma_steps_ExtnR)
  finally show ?case .
next
  case (ParLamComp U U' V V' x)
  have nV: "is_sigma_normal V" using ParLamComp.hyps(2) by (rule par_step_source_normal)
  have nU': "is_sigma_normal U'" using ParLamComp.hyps(1) by (rule par_step_target_normal)
  have "Comp (Lam x U) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* Comp (Lam x U') V"
    using ParLamComp.IH(1) nV ParLamComp.hyps(3) by (rule beta_over_sigma_steps_CompL_Lam)
  also have "Comp (Lam x U') V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Lam x U') V')"
    using ParLamComp.IH(2) nV ParLamComp.hyps(3) nU'
    by (rule beta_over_sigma_steps_CompR_Lam)
  finally show ?case .
next
  case (ParVarComp W W' x)
  have nW: "is_sigma_normal W" using ParVarComp.hyps(1) by (rule par_step_source_normal)
  have nComp: "is_sigma_normal (Comp (Var x) W)"
    by (intro is_sigma_normal.NF_CompVar nW ParVarComp.hyps(2,3))
  have src: "sigma_nf (Comp (Var x) W) = Comp (Var x) W" using nComp by (rule sigma_nf_of_normal)
  have "sigma_nf (Comp (Var x) W) \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp (Var x) W')"
    using ParVarComp.IH nW by (rule beta_over_sigma_steps_CompR_Var)
  then show ?case unfolding src .
next
  case (ParBeta U U' V V' x)
  have nV: "is_sigma_normal V" using ParBeta.hyps(2) by (rule par_step_source_normal)
  have nU: "is_sigma_normal U" using ParBeta.hyps(1) by (rule par_step_source_normal)
  have nU': "is_sigma_normal U'" using ParBeta.hyps(1) by (rule par_step_target_normal)
  have nV': "is_sigma_normal V'" using ParBeta.hyps(2) by (rule par_step_target_normal)
  have nLamU: "is_sigma_normal (Lam x U)" using nU by (rule is_sigma_normal.NF_Lam)
  have "App (Lam x U) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Lam x U) V'"
    using ParBeta.IH(2) nLamU by (rule beta_over_sigma_steps_AppR)
  also have "App (Lam x U) V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Lam x U') V'"
    using beta_over_sigma_steps_Lam [OF ParBeta.IH(1), where x=x] nV'
    by (rule beta_over_sigma_steps_AppL)
  also have "App (Lam x U') V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp U' (Ext V' x Id))"
    using beta_over_sigma_step_Beta by (rule r_into_rtranclp)
  finally show ?case .
next
  case (ParBetaClos U U' V V' W W' x)
  have nV: "is_sigma_normal V" using ParBetaClos.hyps(2) by (rule par_step_source_normal)
  have nU: "is_sigma_normal U" using ParBetaClos.hyps(1) by (rule par_step_source_normal)
  have nW: "is_sigma_normal W" using ParBetaClos.hyps(3) by (rule par_step_source_normal)
  have nV': "is_sigma_normal V'" using ParBetaClos.hyps(2) by (rule par_step_target_normal)
  have nU': "is_sigma_normal U'" using ParBetaClos.hyps(1) by (rule par_step_target_normal)
  have nW': "is_sigma_normal W'" using ParBetaClos.hyps(3) by (rule par_step_target_normal)
  note Wneq = ParBetaClos.hyps(4)
  have nCompLamW: "is_sigma_normal (Comp (Lam x U) W)"
    by (intro is_sigma_normal.NF_CompLam nU nW Wneq)
  have "App (Comp (Lam x U) W) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Comp (Lam x U) W) V'"
    using ParBetaClos.IH(2) nCompLamW by (rule beta_over_sigma_steps_AppR)
  also have "App (Comp (Lam x U) W) V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Comp (Lam x U') W) V'"
    using beta_over_sigma_steps_CompL_Lam [OF ParBetaClos.IH(1) nW Wneq] nV'
    by (rule beta_over_sigma_steps_AppL)
  also have "App (Comp (Lam x U') W) V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (sigma_nf (Comp (Lam x U') W')) V'"
    using beta_over_sigma_steps_CompR_Lam [OF ParBetaClos.IH(3) nW Wneq nU'] nV'
    by (rule beta_over_sigma_steps_AppL)
  also have "App (sigma_nf (Comp (Lam x U') W')) V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp U' (Ext V' x W'))"
  proof (cases "W' = Id")
    case False
    have Wn: "sigma_nf (Comp (Lam x U') W') = Comp (Lam x U') W'"
      by (intro sigma_nf_of_normal is_sigma_normal.NF_CompLam nU' nW' False)
    show ?thesis
      unfolding Wn
      using beta_over_sigma_step_BetaClos by (rule r_into_rtranclp)
  next
    case True
    have Wn: "sigma_nf (Comp (Lam x U') W') = Lam x U'"
      unfolding True
      by (simp add: sigma_nf_Comp_IdR sigma_nf_of_normal [OF is_sigma_normal.NF_Lam [OF nU']])
    show ?thesis
      unfolding Wn
      unfolding True
      using beta_over_sigma_step_Beta by (rule r_into_rtranclp)
  qed
  finally show ?case .
next
  case (ParCompEps U U' V V')
  have nV: "is_sigma_normal V" using ParCompEps.hyps(2) by (rule par_step_source_normal)
  have nU: "is_sigma_normal U" using ParCompEps.hyps(1) by (rule par_step_source_normal)
  have nU': "is_sigma_normal U'" using ParCompEps.hyps(1) by (rule par_step_target_normal)
  have nV': "is_sigma_normal V'" using ParCompEps.hyps(2) by (rule par_step_target_normal)
  have nEpsU: "is_sigma_normal (Eps U)" using nU by (rule is_sigma_normal.NF_Eps)
  have "App (Eps U) V \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Eps U) V'"
    using ParCompEps.IH(2) nEpsU by (rule beta_over_sigma_steps_AppR)
  also have "App (Eps U) V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* App (Eps U') V'"
    using ParCompEps.IH(1) [THEN beta_over_sigma_steps_Eps] nV'
    by (rule beta_over_sigma_steps_AppL)
  also have "App (Eps U') V' \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* sigma_nf (Comp U' V')"
    using beta_over_sigma_step_CompEps by (rule r_into_rtranclp)
  finally show ?case .
qed

end
