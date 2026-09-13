theory EnvEps_Sigma_Assoc_Peak
  imports EnvEps_Sigma_Congruence
begin

text \<open>
  The @{text Assoc} critical-pair family, factored out.

  Every critical pair of @{text "\<rightarrow>\<sigma>"} in which @{text Assoc} fires at the
  root against a step inside its own left argument has the shape

  @{text "Comp Y C  \<leftarrow>  Comp (Comp A B) C  \<rightarrow>  Comp A (Comp B C)"}

  where @{term "Comp A B \<rightarrow>\<sigma> Y"}. This single lemma joins all of them, by
  inverting that inner step. It is used twice in
  @{text EnvEps_Sigma_Local_Confluence}: once in the @{text Assoc} case
  (where the competing step is a @{text CompL}) and once in the
  @{text CompL} case (where the competing step is the @{text Assoc}) --
  the same critical pair reached from its two sides. Proving it once here
  halves the case analysis there.

  Its sub-cases are, in the numbering of
  @{text "docs/enve-sigma-reduction-local-confluence.md"}: @{text Assoc}
  = (2.21), @{text IdL} = (2.22), @{text IdR} = (2.23) first instance,
  @{text VarRef} = (2.26), @{text VarSkip} = (2.27), @{text DApp} =
  (2.28), @{text EpsEps} = (2.30), plus the two structural cases
  (@{text CompL}, @{text CompR}) and one further case, @{text DExtn},
  discussed next.

  \<^bold>\<open>A critical pair missing from the docs.\<close> The docs enumerate exactly
  eleven critical pairs, (2.21)-(2.31), but the @{text DExtn} sub-case
  below -- peak @{term "Comp (Comp (Ext L z M) N) C"}, joinable at
  @{term "Ext (Comp L (Comp N C)) z (Comp M (Comp N C))"} -- is not among
  them, even though it arises in exactly the same way as (2.26)-(2.28)
  and (2.30) do: a base rule firing inside @{text Assoc}'s left argument,
  here @{text DExtn} because that argument is @{text Ext}-headed.
  Formalizing forced the case to surface. It \<^emph>\<open>is\<close> joinable, as shown
  below, so the local-confluence theorem itself is unaffected; only the
  docs' claim to have enumerated every critical pair needs amending.

  The source term is kept as a variable @{term X} with an explicit
  equation @{term "X = Comp A B"}, so that inverting the step by
  @{text sigma_step.induct} leaves every rule's own parameters free and
  substitutes @{term Y} automatically.
\<close>

lemma assoc_peak_join:
  assumes "X \<rightarrow>\<sigma> Y" and "X = Comp A B"
  shows "\<exists>L. Comp Y C \<rightarrow>\<sigma>\<^sup>* L \<and> Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: A B rule: sigma_step.induct)
  case (Assoc P Q R)
  \<comment> \<open>(2.21) @{text Assoc} / @{text Assoc}.\<close>
  then have eq: "A = Comp P Q" "B = R" by auto
  have l: "Comp (Comp P (Comp Q R)) C \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q (Comp R C))"
    by (rule sigma_2 [OF sigma_step.Assoc sigma_step.CompR [OF sigma_step.Assoc]])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q (Comp R C))"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  from l r show ?case by blast
next
  case (IdL P)
  \<comment> \<open>(2.22) @{text IdL} / @{text Assoc}.\<close>
  then have eq: "A = Id" "B = P" by auto
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P C"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.IdL])
  from r show ?case by blast
next
  case (IdR P)
  \<comment> \<open>(2.23), first instance. The joining step on the right is @{text IdL},
      not @{text IdR} -- the mislabelling the docs correct.\<close>
  then have eq: "A = P" "B = Id" by auto
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P C"
    unfolding eq
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF sigma_step.IdL]])
  from r show ?case by blast
next
  case (DExtn L1 z M1 N1)
  \<comment> \<open>The critical pair missing from the docs' eleven; see the theory header.\<close>
  then have eq: "A = Ext L1 z M1" "B = N1" by auto
  have l: "Comp (Ext (Comp L1 N1) z (Comp M1 N1)) C
             \<rightarrow>\<sigma>\<^sup>* Ext (Comp L1 (Comp N1 C)) z (Comp M1 (Comp N1 C))"
    by (rule sigma_3 [OF sigma_step.DExtn
                         sigma_step.ExtnL [OF sigma_step.Assoc]
                         sigma_step.ExtnR [OF sigma_step.Assoc]])
  have r: "Comp A (Comp B C)
             \<rightarrow>\<sigma>\<^sup>* Ext (Comp L1 (Comp N1 C)) z (Comp M1 (Comp N1 C))"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.DExtn])
  from l r show ?case by blast
next
  case (VarRef z P Q)
  \<comment> \<open>(2.26) @{text VarRef} / @{text Assoc}.\<close>
  then have eq: "A = Var z" "B = Ext P z Q" by auto
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P C"
    unfolding eq
    by (rule sigma_2 [OF sigma_step.CompR [OF sigma_step.DExtn] sigma_step.VarRef])
  from r show ?case by blast
next
  case (VarSkip z w P Q)
  \<comment> \<open>(2.27) @{text VarSkip} / @{text Assoc}.\<close>
  from VarSkip have neq: "z \<noteq> w" and eq: "A = Var z" "B = Ext P w Q" by auto
  have l: "Comp (Comp (Var z) Q) C \<rightarrow>\<sigma>\<^sup>* Comp (Var z) (Comp Q C)"
    by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp (Var z) (Comp Q C)"
    unfolding eq
    by (rule sigma_2 [OF sigma_step.CompR [OF sigma_step.DExtn]
                         sigma_step.VarSkip [OF neq]])
  from l r show ?case by blast
next
  case (DApp P Q R)
  \<comment> \<open>(2.28) @{text DApp} / @{text Assoc}.\<close>
  then have eq: "A = App P Q" "B = R" by auto
  have l: "Comp (App (Comp P R) (Comp Q R)) C
             \<rightarrow>\<sigma>\<^sup>* App (Comp P (Comp R C)) (Comp Q (Comp R C))"
    by (rule sigma_3 [OF sigma_step.DApp
                         sigma_step.AppL [OF sigma_step.Assoc]
                         sigma_step.AppR [OF sigma_step.Assoc]])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* App (Comp P (Comp R C)) (Comp Q (Comp R C))"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.DApp])
  from l r show ?case by blast
next
  case (EpsEps P R)
  \<comment> \<open>(2.30) @{text EpsEps} / @{text Assoc}.\<close>
  then have eq: "A = Eps P" "B = R" by auto
  have l: "Comp (Eps P) C \<rightarrow>\<sigma>\<^sup>* Eps P"
    by (rule sigma_step_into_steps [OF sigma_step.EpsEps])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Eps P"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.EpsEps])
  from l r show ?case by blast
next
  case (AppL M M' N)
  then show ?case by simp
next
  case (AppR N N' M)
  then show ?case by simp
next
  case (Lam M M' x)
  then show ?case by simp
next
  case (ExtnL M M' x N)
  then show ?case by simp
next
  case (ExtnR N N' M x)
  then show ?case by simp
next
  case (CompL P P' Q)
  \<comment> \<open>Structural: the inner step is on @{text Assoc}'s own left argument.\<close>
  from CompL have step: "P \<rightarrow>\<sigma> P'" and eq: "A = P" "B = Q" by auto
  have l: "Comp (Comp P' Q) C \<rightarrow>\<sigma>\<^sup>* Comp P' (Comp Q C)"
    by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P' (Comp Q C)"
    unfolding eq by (rule sigma_step_into_steps [OF sigma_step.CompL [OF step]])
  from l r show ?case by blast
next
  case (CompR Q Q' P)
  \<comment> \<open>Structural: the inner step is on @{text Assoc}'s own middle argument.\<close>
  from CompR have step: "Q \<rightarrow>\<sigma> Q'" and eq: "A = P" "B = Q" by auto
  have l: "Comp (Comp P Q') C \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q' C)"
    by (rule sigma_step_into_steps [OF sigma_step.Assoc])
  have r: "Comp A (Comp B C) \<rightarrow>\<sigma>\<^sup>* Comp P (Comp Q' C)"
    unfolding eq
    by (rule sigma_step_into_steps
             [OF sigma_step.CompR [OF sigma_step.CompL [OF step]]])
  from l r show ?case by blast
next
  case (Eop M M')
  then show ?case by simp
qed

end
