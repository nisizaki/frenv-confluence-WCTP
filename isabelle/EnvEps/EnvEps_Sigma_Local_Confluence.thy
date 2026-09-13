theory EnvEps_Sigma_Local_Confluence
  imports EnvEps_Sigma_Root_Peaks
begin

text \<open>
  Local confluence of @{text "\<rightarrow>\<sigma>"} on @{text "lambda_EnvEps"} (docs file
  @{text "docs/enve-sigma-reduction-local-confluence.md"}, thesis Lemma 5,
  presented there as a Theorem; roadmap item 11).

  The proof is by induction on the derivation of the first step, with one
  case per rule of @{text "\<rightarrow>\<sigma>"}. Each case is discharged by the matching
  peak lemma of @{text EnvEps_Sigma_Root_Peaks}, which inverts the
  competing second step and exhibits the join. The critical pairs
  themselves live there and in @{text EnvEps_Sigma_Assoc_Peak} /
  @{text EnvEps_Sigma_Inner_Peaks}; this theory is only the assembly.

  \<^bold>\<open>Finding: the docs' critical-pair enumeration is incomplete.\<close> The docs
  list eleven critical pairs, (2.21)-(2.31). Formalizing surfaced a
  twelfth, @{text DExtn} inside @{text Assoc} -- peak
  @{term "Comp (Comp (Ext L z M) N) C"} -- which arises exactly as
  (2.26)-(2.28) and (2.30) do but is not among them; see the header of
  @{text EnvEps_Sigma_Assoc_Peak}. It is joinable, so the theorem below
  is unaffected, but the docs' claim to have enumerated every critical
  pair should be amended.

  The "disjoint positions commute" case, which the docs state as a single
  general fact rather than checking per rule pair, is not a separate case
  here: it is subsumed by the congruence cases below, where the induction
  hypothesis joins the two reducts of the shared subterm and the
  congruence closure lemmas
  (@{text EnvEps_Sigma_Congruence}) transport that join outwards.
\<close>

theorem sigma_locally_confluent:
  assumes "M \<rightarrow>\<sigma> N\<^sub>1" and "M \<rightarrow>\<sigma> N\<^sub>2"
  shows "\<exists>L. N\<^sub>1 \<rightarrow>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: N\<^sub>2 rule: sigma_step.induct)
  case (Assoc A B C)
  from assoc_root_peak [OF Assoc.prems refl] show ?case .
next
  case (IdL A)
  from idL_root_peak [OF IdL.prems refl] show ?case .
next
  case (IdR A)
  from idR_root_peak [OF IdR.prems refl] show ?case .
next
  case (DExtn P z Q R)
  from dExtn_root_peak [OF DExtn.prems refl] show ?case .
next
  case (VarRef z P Q)
  from varRef_root_peak [OF VarRef.prems refl] show ?case .
next
  case (VarSkip z w P Q)
  from varSkip_root_peak [OF VarSkip.prems refl VarSkip.hyps(1)] show ?case .
next
  case (DApp P Q R)
  from dApp_root_peak [OF DApp.prems refl] show ?case .
next
  case (EpsEps P R)
  from epsEps_root_peak [OF EpsEps.prems refl] show ?case .
next
  case (AppL A A' B)
  from appL_peak [OF AppL.prems refl AppL.hyps(1) AppL.IH] show ?case .
next
  case (AppR B B' A)
  from appR_peak [OF AppR.prems refl AppR.hyps(1) AppR.IH] show ?case .
next
  case (Lam A A' x)
  from lam_peak [OF Lam.prems refl Lam.hyps(1) Lam.IH] show ?case .
next
  case (ExtnL A A' x B)
  from extnL_peak [OF ExtnL.prems refl ExtnL.hyps(1) ExtnL.IH] show ?case .
next
  case (ExtnR B B' A x)
  from extnR_peak [OF ExtnR.prems refl ExtnR.hyps(1) ExtnR.IH] show ?case .
next
  case (CompL A A' B)
  from compL_peak [OF CompL.prems refl CompL.hyps(1) CompL.IH] show ?case .
next
  case (CompR B B' A)
  from compR_peak [OF CompR.prems refl CompR.hyps(1) CompR.IH] show ?case .
next
  case (Eop A A')
  from eop_peak [OF Eop.prems refl Eop.hyps(1) Eop.IH] show ?case .
qed

end
