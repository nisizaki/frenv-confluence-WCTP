theory EnvEps_Sigma_Inner_Peaks
  imports EnvEps_Sigma_Congruence
begin

text \<open>
  Small peak lemmas for the remaining "base rule at the root versus a step
  inside its left argument" families, factored out of
  @{text EnvEps_Sigma_Local_Confluence} in the same way, and for the same
  reason, as @{text EnvEps_Sigma_Assoc_Peak.assoc_peak_join}: each is
  needed twice there, once from either side of the same critical pair.

  Unlike the @{text Assoc} family these invert a step whose source is
  @{text Ext}-, @{text App}- or @{text Eps}-headed, so only the one or two
  matching congruence rules can fire and each proof is short.

  As in @{text EnvEps_Sigma_Assoc_Peak}, the source is kept as a variable
  with an explicit shape equation so that @{text sigma_step.induct} leaves
  every rule's parameters free.
\<close>

text \<open>@{text DExtn} at the root versus a step inside the extension.\<close>

lemma ext_inner_peak:
  assumes "X \<rightarrow>\<sigma> W" and "X = Ext P z Q"
  shows "\<exists>L. Comp W R \<rightarrow>\<sigma>\<^sup>* L \<and> Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P z Q rule: sigma_step.induct)
  case (ExtnL M M' x N)
  note step = ExtnL.hyps(1)
  from ExtnL have eq: "P = M" "z = x" "Q = N" by auto
  have l: "Comp (Ext M' x N) R \<rightarrow>\<sigma>\<^sup>* Ext (Comp M' R) x (Comp N R)"
    by (rule sigma_step_into_steps [OF sigma_step.DExtn])
  have r: "Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Ext (Comp M' R) x (Comp N R)"
    unfolding eq
    by (rule sigma_step_into_steps
             [OF sigma_step.ExtnL [OF sigma_step.CompL [OF step]]])
  from l r show ?case by blast
next
  case (ExtnR N N' M x)
  note step = ExtnR.hyps(1)
  from ExtnR have eq: "P = M" "z = x" "Q = N" by auto
  have l: "Comp (Ext M x N') R \<rightarrow>\<sigma>\<^sup>* Ext (Comp M R) x (Comp N' R)"
    by (rule sigma_step_into_steps [OF sigma_step.DExtn])
  have r: "Ext (Comp P R) z (Comp Q R) \<rightarrow>\<sigma>\<^sup>* Ext (Comp M R) x (Comp N' R)"
    unfolding eq
    by (rule sigma_step_into_steps
             [OF sigma_step.ExtnR [OF sigma_step.CompL [OF step]]])
  from l r show ?case by blast
qed simp_all

text \<open>@{text DApp} at the root versus a step inside the application.\<close>

lemma app_inner_peak:
  assumes "X \<rightarrow>\<sigma> W" and "X = App P Q"
  shows "\<exists>L. Comp W R \<rightarrow>\<sigma>\<^sup>* L \<and> App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P Q rule: sigma_step.induct)
  case (AppL M M' N)
  note step = AppL.hyps(1)
  from AppL have eq: "P = M" "Q = N" by auto
  have l: "Comp (App M' N) R \<rightarrow>\<sigma>\<^sup>* App (Comp M' R) (Comp N R)"
    by (rule sigma_step_into_steps [OF sigma_step.DApp])
  have r: "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App (Comp M' R) (Comp N R)"
    unfolding eq
    by (rule sigma_step_into_steps
             [OF sigma_step.AppL [OF sigma_step.CompL [OF step]]])
  from l r show ?case by blast
next
  case (AppR N N' M)
  note step = AppR.hyps(1)
  from AppR have eq: "P = M" "Q = N" by auto
  have l: "Comp (App M N') R \<rightarrow>\<sigma>\<^sup>* App (Comp M R) (Comp N' R)"
    by (rule sigma_step_into_steps [OF sigma_step.DApp])
  have r: "App (Comp P R) (Comp Q R) \<rightarrow>\<sigma>\<^sup>* App (Comp M R) (Comp N' R)"
    unfolding eq
    by (rule sigma_step_into_steps
             [OF sigma_step.AppR [OF sigma_step.CompL [OF step]]])
  from l r show ?case by blast
qed simp_all

text \<open>@{text EpsEps} at the root versus a step inside the abstraction.\<close>

lemma eps_inner_peak:
  assumes "X \<rightarrow>\<sigma> W" and "X = Eps P"
  shows "\<exists>L. Comp W R \<rightarrow>\<sigma>\<^sup>* L \<and> Eps P \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P rule: sigma_step.induct)
  case (Eop M M')
  note step = Eop.hyps(1)
  from Eop have eq: "P = M" by auto
  have l: "Comp (Eps M') R \<rightarrow>\<sigma>\<^sup>* Eps M'"
    by (rule sigma_step_into_steps [OF sigma_step.EpsEps])
  have r: "Eps P \<rightarrow>\<sigma>\<^sup>* Eps M'"
    unfolding eq
    by (rule sigma_step_into_steps [OF sigma_step.Eop [OF step]])
  from l r show ?case by blast
qed simp_all

text \<open>
  @{text VarRef} at the root versus a step inside the environment it looks
  the variable up in.
\<close>

lemma var_ref_inner_peak:
  assumes "X \<rightarrow>\<sigma> W" and "X = Ext P z Q"
  shows "\<exists>L. Comp (Var z) W \<rightarrow>\<sigma>\<^sup>* L \<and> P \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P z Q rule: sigma_step.induct)
  case (ExtnL M M' x N)
  note step = ExtnL.hyps(1)
  from ExtnL have eq: "P = M" "z = x" "Q = N" by auto
  have l: "Comp (Var x) (Ext M' x N) \<rightarrow>\<sigma>\<^sup>* M'"
    by (rule sigma_step_into_steps [OF sigma_step.VarRef])
  have r: "P \<rightarrow>\<sigma>\<^sup>* M'"
    unfolding eq by (rule sigma_step_into_steps [OF step])
  from l r eq show ?case by auto
next
  case (ExtnR N N' M x)
  from ExtnR have eq: "P = M" "z = x" "Q = N" by auto
  have l: "Comp (Var x) (Ext M x N') \<rightarrow>\<sigma>\<^sup>* M"
    by (rule sigma_step_into_steps [OF sigma_step.VarRef])
  from l eq show ?case by auto
qed simp_all

text \<open>
  @{text VarSkip} at the root versus a step inside the environment it skips
  a binding of.
\<close>

lemma var_skip_inner_peak:
  assumes "X \<rightarrow>\<sigma> W" and "X = Ext P w Q" and "z \<noteq> w"
  shows "\<exists>L. Comp (Var z) W \<rightarrow>\<sigma>\<^sup>* L \<and> Comp (Var z) Q \<rightarrow>\<sigma>\<^sup>* L"
  using assms
proof (induction arbitrary: P w Q rule: sigma_step.induct)
  case (ExtnL M M' x N)
  from ExtnL have eq: "P = M" "w = x" "Q = N" and neq: "z \<noteq> x" by auto
  have l: "Comp (Var z) (Ext M' x N) \<rightarrow>\<sigma>\<^sup>* Comp (Var z) N"
    by (rule sigma_step_into_steps [OF sigma_step.VarSkip [OF neq]])
  from l eq show ?case by auto
next
  case (ExtnR N N' M x)
  note step = ExtnR.hyps(1)
  from ExtnR have eq: "P = M" "w = x" "Q = N" and neq: "z \<noteq> x" by auto
  have l: "Comp (Var z) (Ext M x N') \<rightarrow>\<sigma>\<^sup>* Comp (Var z) N'"
    by (rule sigma_step_into_steps [OF sigma_step.VarSkip [OF neq]])
  have r: "Comp (Var z) Q \<rightarrow>\<sigma>\<^sup>* Comp (Var z) N'"
    unfolding eq
    by (rule sigma_step_into_steps [OF sigma_step.CompR [OF step]])
  from l r show ?case by blast
qed simp_all

end
