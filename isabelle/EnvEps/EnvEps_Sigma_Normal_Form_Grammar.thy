theory EnvEps_Sigma_Normal_Form_Grammar
  imports EnvEps_Sigma_Normal_Form
begin

text \<open>
  The grammar (2.32) of @{text "\<sigma>"}-normal forms (docs file
  @{text "docs/enve-sigma-normal-form-grammar.md"}, thesis Theorem 6,
  presented there as a Lemma; roadmap item 14), formalized as an
  inductive predicate @{text is_sigma_normal} mirroring the eight
  productions, and proved equivalent to @{text sigma_irreducible}
  (@{text "EnvEps_Sigma_Normal_Form.sigma_irreducible"}).
\<close>

inductive is_sigma_normal :: "trm \<Rightarrow> bool" where
  NF_Id:   "is_sigma_normal Id"
| NF_Var:  "is_sigma_normal (Var x)"
| NF_Lam:  "is_sigma_normal U \<Longrightarrow> is_sigma_normal (Lam x U)"
| NF_App:  "is_sigma_normal U1 \<Longrightarrow> is_sigma_normal U2
            \<Longrightarrow> is_sigma_normal (App U1 U2)"
| NF_Ext:  "is_sigma_normal U1 \<Longrightarrow> is_sigma_normal U2
            \<Longrightarrow> is_sigma_normal (Ext U1 x U2)"
| NF_Eps:  "is_sigma_normal U \<Longrightarrow> is_sigma_normal (Eps U)"
| NF_CompLam:
    "is_sigma_normal U1 \<Longrightarrow> is_sigma_normal U3 \<Longrightarrow> U3 \<noteq> Id
     \<Longrightarrow> is_sigma_normal (Comp (Lam x U1) U3)"
| NF_CompVar:
    "is_sigma_normal W \<Longrightarrow> W \<noteq> Id \<Longrightarrow> (\<nexists>P y Q. W = Ext P y Q)
     \<Longrightarrow> is_sigma_normal (Comp (Var x) W)"

text \<open>Specialized elimination rules for @{text "\<rightarrow>\<sigma>"} on each of the shapes
      appearing in the grammar, used to show grammar terms are
      irreducible.\<close>

inductive_cases sigma_step_IdE [elim]: "Id \<rightarrow>\<sigma> N"
inductive_cases sigma_step_VarE [elim]: "Var x \<rightarrow>\<sigma> N"
inductive_cases sigma_step_LamE [elim]: "Lam x U \<rightarrow>\<sigma> N"
inductive_cases sigma_step_AppE [elim]: "App U1 U2 \<rightarrow>\<sigma> N"
inductive_cases sigma_step_ExtE [elim]: "Ext U1 x U2 \<rightarrow>\<sigma> N"
inductive_cases sigma_step_EpsE [elim]: "Eps U \<rightarrow>\<sigma> N"
inductive_cases sigma_step_Comp_LamE [elim]:
  "Comp (Lam x U1) U3 \<rightarrow>\<sigma> N"
inductive_cases sigma_step_Comp_VarE [elim]:
  "Comp (Var x) W \<rightarrow>\<sigma> N"

lemma is_sigma_normal_imp_irreducible:
  assumes "is_sigma_normal M"
  shows "sigma_irreducible M"
  using assms
proof (induction rule: is_sigma_normal.induct)
  case NF_Id
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_Var x)
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_Lam U x)
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_App U1 U2)
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_Ext U1 U2 x)
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_Eps U)
  then show ?case by (auto simp: sigma_irreducible_def)
next
  case (NF_CompLam U1 U3 x)
  then show ?case
    by (auto simp: sigma_irreducible_def elim!: sigma_step_Comp_LamE)
next
  case (NF_CompVar W x)
  then show ?case
    by (auto simp: sigma_irreducible_def elim!: sigma_step_Comp_VarE)
qed

lemma sigma_irreducible_imp_is_sigma_normal:
  assumes "sigma_irreducible M"
  shows "is_sigma_normal M"
  using assms
proof (induction M)
  case Id
  then show ?case by (auto intro: is_sigma_normal.intros)
next
  case (Var x)
  then show ?case by (auto intro: is_sigma_normal.intros)
next
  case (App M1 M2)
  have "sigma_irreducible M1" "sigma_irreducible M2"
    using App.prems by (auto simp: sigma_irreducible_def intro: sigma_step.AppL sigma_step.AppR)
  with App.IH show ?case by (auto intro: is_sigma_normal.intros)
next
  case (Ext M1 x M2)
  have "sigma_irreducible M1" "sigma_irreducible M2"
    using Ext.prems by (auto simp: sigma_irreducible_def intro: sigma_step.ExtnL sigma_step.ExtnR)
  with Ext.IH show ?case by (auto intro: is_sigma_normal.intros)
next
  case (Lam x M1)
  have "sigma_irreducible M1"
    using Lam.prems by (auto simp: sigma_irreducible_def intro: sigma_step.Lam)
  with Lam.IH show ?case by (auto intro: is_sigma_normal.intros)
next
  case (Eps M1)
  have "sigma_irreducible M1"
    using Eps.prems by (auto simp: sigma_irreducible_def intro: sigma_step.Eop)
  with Eps.IH show ?case by (auto intro: is_sigma_normal.intros)
next
  case (Comp M1 M2)
  have irr1: "sigma_irreducible M1" and irr2: "sigma_irreducible M2"
    using Comp.prems
    by (auto simp: sigma_irreducible_def intro: sigma_step.CompL sigma_step.CompR)
  have nf1: "is_sigma_normal M1" and nf2: "is_sigma_normal M2"
    using Comp.IH irr1 irr2 by auto
  have not_id2: "M2 \<noteq> Id"
    using Comp.prems by (auto simp: sigma_irreducible_def intro: sigma_step.IdR)
  from nf1 show ?case
  proof (cases rule: is_sigma_normal.cases)
    case NF_Id
    then have "Comp M1 M2 \<rightarrow>\<sigma> M2" by (auto intro: sigma_step.IdL)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  next
    case (NF_Var x)
    have not_ext: "\<nexists>P y Q. M2 = Ext P y Q"
    proof (rule notI)
      assume "\<exists>P y Q. M2 = Ext P y Q"
      then obtain P y Q where "M2 = Ext P y Q" by blast
      then have "Comp M1 M2 \<rightarrow>\<sigma> (if x = y then P else Comp (Var x) Q)"
        using NF_Var by (auto intro: sigma_step.VarRef sigma_step.VarSkip)
      with Comp.prems show False by (auto simp: sigma_irreducible_def)
    qed
    show ?thesis
      using NF_Var not_id2 not_ext nf2 by (auto intro: is_sigma_normal.NF_CompVar)
  next
    case (NF_Lam U x)
    show ?thesis
      using NF_Lam not_id2 nf2 by (auto intro: is_sigma_normal.NF_CompLam)
  next
    case (NF_App U1 U2)
    then have "Comp M1 M2 \<rightarrow>\<sigma> App (Comp U1 M2) (Comp U2 M2)"
      by (auto intro: sigma_step.DApp)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  next
    case (NF_Ext U1 U2 x)
    then have "Comp M1 M2 \<rightarrow>\<sigma> Ext (Comp U1 M2) x (Comp U2 M2)"
      by (auto intro: sigma_step.DExtn)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  next
    case (NF_Eps U)
    then have "Comp M1 M2 \<rightarrow>\<sigma> Eps U" by (auto intro: sigma_step.EpsEps)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  next
    case (NF_CompLam U1 U3 x)
    then have "Comp M1 M2 \<rightarrow>\<sigma> Comp (Lam x U1) (Comp U3 M2)"
      by (auto intro: sigma_step.Assoc)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  next
    case (NF_CompVar W x)
    then have "Comp M1 M2 \<rightarrow>\<sigma> Comp (Var x) (Comp W M2)"
      by (auto intro: sigma_step.Assoc)
    with Comp.prems show ?thesis by (auto simp: sigma_irreducible_def)
  qed
qed

theorem sigma_normal_form_grammar:
  "is_sigma_normal M \<longleftrightarrow> sigma_irreducible M"
  using is_sigma_normal_imp_irreducible sigma_irreducible_imp_is_sigma_normal by blast

text \<open>
  The @{text "\<sigma>"}-normal form of any term is, in particular, in the
  grammar. Stated as its own (intro-shaped) fact so that goals of the
  form @{term "is_sigma_normal (sigma_nf M)"} -- which arise for every
  @{text "\<sigma>"}-renormalizing rule of @{text "\<Rightarrow>par"} -- close directly,
  without unfolding @{const is_sigma_normal} into
  @{const sigma_irreducible} and thereby disabling the structural
  introduction rules.
\<close>

lemma is_sigma_normal_sigma_nf [simp, intro]: "is_sigma_normal (sigma_nf M)"
  using sigma_nf_irreducible by (simp add: sigma_normal_form_grammar)

end
