theory EnvEps_Sigma_Congruence
  imports EnvEps_Sigma
begin

text \<open>
  Congruence closure of @{text "\<rightarrow>\<sigma>\<^sup>*"}: each of the eight congruence
  rules of @{text "\<rightarrow>\<sigma>"} lifts from a single step to a whole chain. These
  are the "context monotonicity" facts that every joining sequence in the
  local-confluence proof (@{text EnvEps_Sigma_Local_Confluence}) is built
  from, so they are collected here once, as introduction rules, rather
  than being re-derived per critical pair.
\<close>

lemma sigma_steps_AppL [intro]: "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> App M N \<rightarrow>\<sigma>\<^sup>* App M' N"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.AppL rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_AppR [intro]: "N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> App M N \<rightarrow>\<sigma>\<^sup>* App M N'"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.AppR rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_Lam [intro]: "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> Lam x M \<rightarrow>\<sigma>\<^sup>* Lam x M'"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.Lam rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_ExtnL [intro]: "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> Ext M x N \<rightarrow>\<sigma>\<^sup>* Ext M' x N"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.ExtnL rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_ExtnR [intro]: "N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> Ext M x N \<rightarrow>\<sigma>\<^sup>* Ext M x N'"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.ExtnR rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_CompL [intro]: "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> Comp M N \<rightarrow>\<sigma>\<^sup>* Comp M' N"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.CompL rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_CompR [intro]: "N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> Comp M N \<rightarrow>\<sigma>\<^sup>* Comp M N'"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.CompR rtranclp.rtrancl_into_rtrancl)

lemma sigma_steps_Eop [intro]: "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> Eps M \<rightarrow>\<sigma>\<^sup>* Eps M'"
  by (induction rule: rtranclp.induct)
     (auto intro: sigma_step.Eop rtranclp.rtrancl_into_rtrancl)

text \<open>Two-sided versions, for the binary constructors.\<close>

lemma sigma_steps_App [intro]:
  "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> App M N \<rightarrow>\<sigma>\<^sup>* App M' N'"
  using sigma_steps_AppL sigma_steps_AppR by (blast intro: rtranclp_trans)

lemma sigma_steps_Ext [intro]:
  "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> Ext M x N \<rightarrow>\<sigma>\<^sup>* Ext M' x N'"
  using sigma_steps_ExtnL sigma_steps_ExtnR by (blast intro: rtranclp_trans)

lemma sigma_steps_Comp [intro]:
  "M \<rightarrow>\<sigma>\<^sup>* M' \<Longrightarrow> N \<rightarrow>\<sigma>\<^sup>* N' \<Longrightarrow> Comp M N \<rightarrow>\<sigma>\<^sup>* Comp M' N'"
  using sigma_steps_CompL sigma_steps_CompR by (blast intro: rtranclp_trans)

text \<open>Turning a single step, or a base rule, into a chain.\<close>

lemma sigma_step_into_steps [intro]: "M \<rightarrow>\<sigma> N \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* N"
  by (rule r_into_rtranclp)

lemma sigma_2: "M \<rightarrow>\<sigma> N \<Longrightarrow> N \<rightarrow>\<sigma> L \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* L"
  by (rule converse_rtranclp_into_rtranclp) auto

lemma sigma_3: "M \<rightarrow>\<sigma> N \<Longrightarrow> N \<rightarrow>\<sigma> L \<Longrightarrow> L \<rightarrow>\<sigma> K \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* K"
  by (rule converse_rtranclp_into_rtranclp) (auto intro: sigma_2)

lemma sigma_4: "M \<rightarrow>\<sigma> N \<Longrightarrow> N \<rightarrow>\<sigma> L \<Longrightarrow> L \<rightarrow>\<sigma> K \<Longrightarrow> K \<rightarrow>\<sigma> J \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* J"
  by (rule converse_rtranclp_into_rtranclp) (auto intro: sigma_3)

lemma sigma_step_then_steps: "M \<rightarrow>\<sigma> N \<Longrightarrow> N \<rightarrow>\<sigma>\<^sup>* L \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* L"
  by (rule converse_rtranclp_into_rtranclp)

lemma sigma_steps_then_step: "M \<rightarrow>\<sigma>\<^sup>* N \<Longrightarrow> N \<rightarrow>\<sigma> L \<Longrightarrow> M \<rightarrow>\<sigma>\<^sup>* L"
  by (rule rtranclp.rtrancl_into_rtrancl)

text \<open>
  Shape-based inversion rules for @{text "\<rightarrow>\<sigma>"}, one per head constructor.
  With a concrete head these collapse the sixteen rules to just the few
  that can actually fire, which is what makes the critical-pair analysis
  in @{text EnvEps_Sigma_Local_Confluence} tractable.
\<close>

inductive_cases sigma_VarE:  "Var x \<rightarrow>\<sigma> N"
inductive_cases sigma_IdE:   "Id \<rightarrow>\<sigma> N"
inductive_cases sigma_LamE:  "Lam x M \<rightarrow>\<sigma> N"
inductive_cases sigma_EpsE:  "Eps M \<rightarrow>\<sigma> N"
inductive_cases sigma_AppE:  "App M N \<rightarrow>\<sigma> L"
inductive_cases sigma_ExtE:  "Ext M x N \<rightarrow>\<sigma> L"
inductive_cases sigma_CompE: "Comp M N \<rightarrow>\<sigma> L"

lemma sigma_Var_no_step [simp]: "\<not> (Var x \<rightarrow>\<sigma> N)"
  by (auto elim: sigma_VarE)

lemma sigma_Id_no_step [simp]: "\<not> (Id \<rightarrow>\<sigma> N)"
  by (auto elim: sigma_IdE)

end
