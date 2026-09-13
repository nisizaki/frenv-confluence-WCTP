theory FREnv_BetaSigma_Local_Confluence
  imports FREnv_BetaSigma_Congruence_Peaks
begin

text \<open>
  Local confluence of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} on @{text "lambda_FREnv"}
  (docs file @{text "docs/frenv-beta-sigma-local-confluence.md"}, roadmap
  item 4), by induction on the derivation of the first step, with one
  case per rule of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"}. Each base-rule case is discharged by
  the matching root-peak lemma of @{text FREnv_BetaSigma_Root_Peaks},
  which inverts the competing second step and exhibits the join; each
  congruence-rule case is discharged by the matching lemma of @{text
  FREnv_BetaSigma_Congruence_Peaks}. The 25 critical pairs of the docs
  (@{text R1}-@{text R6}/@{text C1}, @{text A1}-@{text A8}, @{text
  D1}-@{text D10}) all live inside those two theories -- this theory is
  only the assembly, mirroring @{text
  "EnvEps.EnvEps_Sigma_Local_Confluence"}.
\<close>

theorem beta_sigma_step_locally_confluent:
  assumes "M \<rightarrow>\<beta>\<sigma> N\<^sub>1" and "M \<rightarrow>\<beta>\<sigma> N\<^sub>2"
  shows "\<exists>L. N\<^sub>1 \<rightarrow>\<beta>\<sigma>\<^sup>* L \<and> N\<^sub>2 \<rightarrow>\<beta>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: N\<^sub>2 rule: beta_sigma_step.induct)
  case (Beta x M1 N1)
  from beta_root_peak [OF Beta.prems refl] show ?case .
next
  case (BetaClos x M1 L1 N1)
  from betaClos_root_peak [OF BetaClos.prems refl] show ?case .
next
  case (Assoc L1 M1 N1)
  from assoc_root_peak [OF Assoc.prems refl] show ?case .
next
  case (IdL M1)
  from idL_root_peak [OF IdL.prems refl] show ?case .
next
  case (IdR M1)
  from idR_root_peak [OF IdR.prems refl] show ?case .
next
  case (DExtn L1 x M1 N1)
  from dExtn_root_peak [OF DExtn.prems refl] show ?case .
next
  case (VarRef x M1 N1)
  from varRef_root_peak [OF VarRef.prems refl] show ?case .
next
  case (VarSkip x y M1 N1)
  from varSkip_root_peak [OF VarSkip.prems refl VarSkip.hyps(1)] show ?case .
next
  case (DApp M1 N1 L1)
  from dApp_root_peak [OF DApp.prems refl] show ?case .
next
  case (EpsEps M1 N1)
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
  case (EnvAbst A A')
  from envAbst_peak [OF EnvAbst.prems refl EnvAbst.hyps(1) EnvAbst.IH] show ?case .
qed

end
