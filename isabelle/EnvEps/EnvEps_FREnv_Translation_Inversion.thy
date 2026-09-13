theory EnvEps_FREnv_Translation_Inversion
  imports EnvEps_FREnv_Translation
begin

text \<open>
  Inversion lemmas for the translation @{text "\<lbrakk>-\<rbrakk>"}
  (@{text EnvEps_FREnv_Translation}, roadmap item 27): given the shape of
  @{text "\<lbrakk>M\<rbrakk>"}, characterize the possible shapes of @{text M} itself.
  Every @{text "lambda_FREnv"} head except @{text App} has a unique
  @{text "lambda_EnvEps"} preimage constructor, since only
  @{text "EnvEps_Syntax.Comp"} and @{text "EnvEps_Syntax.App"} both
  translate to an @{text "FREnv_Syntax.App"} (@{text "\<lbrakk>Comp M N\<rbrakk> = App (Eps \<lbrakk>M\<rbrakk>) \<lbrakk>N\<rbrakk>"},
  @{text "\<lbrakk>App M N\<rbrakk> = App \<lbrakk>M\<rbrakk> \<lbrakk>N\<rbrakk>"}). Needed by
  @{text EnvEps_FREnv_Translation_Lifting} (roadmap item 30) to invert
  the shape of a @{text "lambda_FREnv"}-side redex back onto the
  @{text "lambda_EnvEps"} side.
\<close>

lemma translate_Var_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.Var x \<Longrightarrow> M = EnvEps_Syntax.Var x"
  by (cases M) auto

lemma translate_Id_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.Id \<Longrightarrow> M = EnvEps_Syntax.Id"
  by (cases M) auto

lemma translate_Lam_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.Lam x A \<Longrightarrow> \<exists>M1. M = EnvEps_Syntax.Lam x M1 \<and> A = \<lbrakk>M1\<rbrakk>"
  by (cases M) auto

lemma translate_Ext_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.Ext A x B
   \<Longrightarrow> \<exists>M1 M2. M = EnvEps_Syntax.Ext M1 x M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
  by (cases M) auto

lemma translate_Eps_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.Eps A \<Longrightarrow> \<exists>M1. M = EnvEps_Syntax.Eps M1 \<and> A = \<lbrakk>M1\<rbrakk>"
  by (cases M) auto

lemma translate_App_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.App A B \<Longrightarrow>
     (\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
   \<or> (\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
  by (cases M) auto

text \<open>
  The recurring pattern: @{text "\<lbrakk>M\<rbrakk> = App (Eps X) Y"} means @{text M} is
  either @{term "Comp M1 M2"} (with @{text "X = \<lbrakk>M1\<rbrakk>"}) or the literal
  @{term "App (Eps M1) M2"} (with @{text "X = \<lbrakk>M1\<rbrakk>"} again) -- in both
  cases @{text "Y = \<lbrakk>M2\<rbrakk>"}. The two are distinguished by whether firing
  @{text "Comp\<^sub>\<epsilon>"} is needed (zero steps for the former, one step for the
  latter) to expose the @{text Comp} shape on the @{text "lambda_EnvEps"}
  side.
\<close>

lemma translate_AppEps_inv:
  "\<lbrakk>M\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps X) Y \<Longrightarrow>
     (\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> X = \<lbrakk>M1\<rbrakk> \<and> Y = \<lbrakk>M2\<rbrakk>)
   \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> X = \<lbrakk>M1\<rbrakk> \<and> Y = \<lbrakk>M2\<rbrakk>)"
  using translate_App_inv [of M "FREnv_Syntax.Eps X" Y] translate_Eps_inv
  by fastforce

end
