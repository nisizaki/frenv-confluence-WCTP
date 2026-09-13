theory EnvEps_FREnv_Translation
  imports EnvEps_Syntax "FREnv.FREnv_Syntax"
begin

text \<open>
  Translation @{text "\<lbrakk>-\<rbrakk> : Term(lambda_EnvEps) \<rightarrow> Term(lambda_FREnv)"}
  (docs file @{text "docs/enve-frenv-translation.md"}, thesis
  Definition 10, equation (2.12); roadmap item 27). Identity on every
  shared constructor; the extra @{text Comp} constructor of
  @{text "lambda_EnvEps"} is eliminated by rewriting @{text "Comp M N"}
  as @{text "App (Eps \<lbrakk>M\<rbrakk>) \<lbrakk>N\<rbrakk>"} in the target @{text "lambda_FREnv"}
  syntax (@{text "FREnv.trm"}, six constructors, no @{text Comp}).
\<close>

fun translate :: "EnvEps_Syntax.trm \<Rightarrow> FREnv_Syntax.trm" ("\<lbrakk>_\<rbrakk>") where
  "\<lbrakk>EnvEps_Syntax.Var x\<rbrakk>       = FREnv_Syntax.Var x"
| "\<lbrakk>EnvEps_Syntax.Id\<rbrakk>          = FREnv_Syntax.Id"
| "\<lbrakk>EnvEps_Syntax.Lam x M\<rbrakk>     = FREnv_Syntax.Lam x \<lbrakk>M\<rbrakk>"
| "\<lbrakk>EnvEps_Syntax.App M N\<rbrakk>     = FREnv_Syntax.App \<lbrakk>M\<rbrakk> \<lbrakk>N\<rbrakk>"
| "\<lbrakk>EnvEps_Syntax.Ext M x N\<rbrakk>   = FREnv_Syntax.Ext \<lbrakk>M\<rbrakk> x \<lbrakk>N\<rbrakk>"
| "\<lbrakk>EnvEps_Syntax.Eps M\<rbrakk>       = FREnv_Syntax.Eps \<lbrakk>M\<rbrakk>"
| "\<lbrakk>EnvEps_Syntax.Comp M N\<rbrakk>    = FREnv_Syntax.App (FREnv_Syntax.Eps \<lbrakk>M\<rbrakk>) \<lbrakk>N\<rbrakk>"

end
