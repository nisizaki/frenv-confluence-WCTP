theory EnvEps_Beta_Over_Sigma
  imports EnvEps_Beta_Step EnvEps_Sigma_Normal_Form_Grammar
begin

text \<open>
  Beta-over-sigma reduction (the doc's slash notation, rendered here with
  a bar instead of a literal slash, which is a reserved pretty-printing
  character in Isabelle mixfix syntax), defined only on sigma-normal
  forms (docs file @{text "docs/enve-beta-over-sigma-reduction.md"},
  thesis Definition 13; roadmap item 15). @{text "U \<rightarrow>\<beta>\<bar>\<sigma> V"} holds iff
  @{text U} takes one @{text "\<rightarrow>\<^sub>\<beta>"} step to some @{text M}, and @{text V}
  is @{text M}'s (unique) sigma-normal form.
\<close>

definition beta_over_sigma_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<bar>\<sigma>" 50) where
  "U \<rightarrow>\<beta>\<bar>\<sigma> V \<longleftrightarrow> (\<exists>M. U \<rightarrow>\<beta> M \<and> M \<rightarrow>\<sigma>\<^sup>* V \<and> is_sigma_normal V)"

text \<open>Equivalent, more direct characterization via @{text sigma_nf}: this
      relies on uniqueness of @{text "\<sigma>"}-normal forms (\<open>sigma_nf_unique\<close>),
      which in turn rests on confluence of @{text "\<rightarrow>\<sigma>"} -- now fully
      proved, so this characterization is unconditional.\<close>

lemma beta_over_sigma_step_iff_sigma_nf:
  "U \<rightarrow>\<beta>\<bar>\<sigma> V \<longleftrightarrow> (\<exists>M. U \<rightarrow>\<beta> M \<and> V = sigma_nf M)"
proof
  assume "U \<rightarrow>\<beta>\<bar>\<sigma> V"
  then obtain M where M: "U \<rightarrow>\<beta> M" "M \<rightarrow>\<sigma>\<^sup>* V" "is_sigma_normal V" by (auto simp: beta_over_sigma_step_def)
  from M(3) have "sigma_irreducible V" by (simp add: sigma_normal_form_grammar)
  with M(2) have "sigma_nf M = V"
    by (rule sigma_nf_eq_if_reduces_and_irreducible)
  then have "V = sigma_nf M" by (rule sym)
  with M(1) show "\<exists>M. U \<rightarrow>\<beta> M \<and> V = sigma_nf M" by blast
next
  assume "\<exists>M. U \<rightarrow>\<beta> M \<and> V = sigma_nf M"
  then obtain M where M: "U \<rightarrow>\<beta> M" "V = sigma_nf M" by blast
  then show "U \<rightarrow>\<beta>\<bar>\<sigma> V"
    using sigma_nf_reduces sigma_nf_irreducible
    by (auto simp: beta_over_sigma_step_def sigma_normal_form_grammar)
qed

abbreviation beta_over_sigma_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<bar>\<sigma>\<^sup>*" 50) where
  "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* V \<equiv> beta_over_sigma_step\<^sup>*\<^sup>* U V"

text \<open>
  Every @{text "\<rightarrow>\<^sub>\<beta>\<bar>\<sigma>"}-step lands on a @{text "\<sigma>"}-normal form -- immediate
  from the definition, which demands it outright -- so normality is
  carried along any chain. Needed to thread the @{text is_sigma_normal}
  hypotheses of the Simulation and Soundness lemmas through the
  chain-length inductions in @{text EnvEps_Beta_Over_Sigma_Confluence}.
\<close>

lemma beta_over_sigma_step_target_normal:
  "U \<rightarrow>\<beta>\<bar>\<sigma> V \<Longrightarrow> is_sigma_normal V"
  by (auto simp: beta_over_sigma_step_def)

lemma beta_over_sigma_steps_target_normal:
  assumes "is_sigma_normal U" and "U \<rightarrow>\<beta>\<bar>\<sigma>\<^sup>* V"
  shows "is_sigma_normal V"
  using assms(2) assms(1)
  by (induction rule: rtranclp.induct) (auto dest: beta_over_sigma_step_target_normal)

end
