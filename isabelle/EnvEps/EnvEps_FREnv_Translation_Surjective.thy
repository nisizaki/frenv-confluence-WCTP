theory EnvEps_FREnv_Translation_Surjective
  imports EnvEps_FREnv_Translation
begin

text \<open>
  Surjectivity of @{text "\<lbrakk>-\<rbrakk>"} (docs file
  @{text "docs/enve-frenv-translation-surjective.md"}, thesis Lemma 1;
  roadmap item 28), via the inclusion @{text incl} (thesis Definition 14)
  from @{text "FREnv.trm"} into @{text "EnvEps.trm"}, satisfying
  @{text "\<lbrakk>incl T\<rbrakk> = T"} for every @{text T}.
\<close>

fun incl :: "FREnv_Syntax.trm \<Rightarrow> EnvEps_Syntax.trm" where
  "incl (FREnv_Syntax.Var x)     = EnvEps_Syntax.Var x"
| "incl FREnv_Syntax.Id          = EnvEps_Syntax.Id"
| "incl (FREnv_Syntax.Lam x M)   = EnvEps_Syntax.Lam x (incl M)"
| "incl (FREnv_Syntax.App M N)   = EnvEps_Syntax.App (incl M) (incl N)"
| "incl (FREnv_Syntax.Ext M x N) = EnvEps_Syntax.Ext (incl M) x (incl N)"
| "incl (FREnv_Syntax.Eps M)     = EnvEps_Syntax.Eps (incl M)"

lemma translate_incl [simp]: "\<lbrakk>incl T\<rbrakk> = T"
  by (induction T) auto

theorem translate_surjective: "\<exists>M. \<lbrakk>M\<rbrakk> = T"
  using translate_incl by blast

end
