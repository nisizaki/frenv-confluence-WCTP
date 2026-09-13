theory EnvEps_Sigma_Length_Decrease
  imports EnvEps_Sigma EnvEps_Term_Length
begin

text \<open>
  Length decrease under @{text "\<rightarrow>\<sigma>"} (docs file
  @{text "docs/enve-sigma-reduction-length-decrease.md"}, thesis
  Theorem 3, presented there as a Lemma).
\<close>

lemma sigma_step_length_decrease:
  assumes "M \<rightarrow>\<sigma> N"
  shows "length_enve M > length_enve N"
  using assms
proof (induction rule: sigma_step.induct)
  case (Assoc M N L)
  then show ?case using length_pos[of M] length_pos[of N] length_pos[of L]
    by (simp add: algebra_simps)
next
  case (IdL M)
  then show ?case by simp
next
  case (IdR M)
  then show ?case using length_pos[of M] by simp
next
  case (DExtn L x M N)
  then show ?case using length_pos[of N]
    by (simp add: algebra_simps)
next
  case (VarRef x M N)
  then show ?case by simp
next
  case (VarSkip x y M N)
  then show ?case by simp
next
  case (DApp M N L)
  then show ?case using length_pos[of L]
    by (simp add: algebra_simps)
next
  case (EpsEps M N)
  then show ?case using length_pos[of M] length_pos[of N]
    by (simp add: algebra_simps)
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
  case (CompL M M' N)
  have "length_enve M' * (length_enve N + 1) < length_enve M * (length_enve N + 1)"
    using CompL.IH by (intro mult_strict_right_mono) simp_all
  then show ?case by (simp add: algebra_simps)
next
  case (CompR N N' M)
  then show ?case using length_pos[of M] by simp
next
  case (Eop M M')
  then show ?case by simp
qed

end
