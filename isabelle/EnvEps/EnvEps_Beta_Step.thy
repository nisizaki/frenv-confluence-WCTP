theory EnvEps_Beta_Step
  imports EnvEps_BetaSigma
begin

text \<open>
  The @{text "\<rightarrow>\<^sub>\<beta>"} fragment of @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} (docs file
  @{text "docs/enve-beta-over-sigma-reduction.md"}, "Preliminary" section):
  the three beta rules @{text Beta}, @{text BetaClos}, @{text "Comp\<^sub>\<epsilon>"}
  plus all eight congruence rules, i.e. @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} with the eight
  substitution rules dropped. So @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma> = \<rightarrow>\<^sub>\<beta> \<union> \<rightarrow>\<sigma>"}.
\<close>

inductive beta_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>" 50) where
  Beta:
    "App (Lam x M) N \<rightarrow>\<beta> Comp M (Ext N x Id)"
| BetaClos:
    "App (Comp (Lam x M) L) N \<rightarrow>\<beta> Comp M (Ext N x L)"
| CompEps:
    "App (Eps M) N \<rightarrow>\<beta> Comp M N"
| AppL:
    "M \<rightarrow>\<beta> M' \<Longrightarrow> App M N \<rightarrow>\<beta> App M' N"
| AppR:
    "N \<rightarrow>\<beta> N' \<Longrightarrow> App M N \<rightarrow>\<beta> App M N'"
| Lam:
    "M \<rightarrow>\<beta> M' \<Longrightarrow> Lam x M \<rightarrow>\<beta> Lam x M'"
| ExtnL:
    "M \<rightarrow>\<beta> M' \<Longrightarrow> Ext M x N \<rightarrow>\<beta> Ext M' x N"
| ExtnR:
    "N \<rightarrow>\<beta> N' \<Longrightarrow> Ext M x N \<rightarrow>\<beta> Ext M x N'"
| CompL:
    "M \<rightarrow>\<beta> M' \<Longrightarrow> Comp M N \<rightarrow>\<beta> Comp M' N"
| CompR:
    "N \<rightarrow>\<beta> N' \<Longrightarrow> Comp M N \<rightarrow>\<beta> Comp M N'"
| Eop:
    "M \<rightarrow>\<beta> M' \<Longrightarrow> Eps M \<rightarrow>\<beta> Eps M'"

abbreviation beta_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<beta>\<^sup>*" 50) where
  "M \<rightarrow>\<beta>\<^sup>* N \<equiv> beta_step\<^sup>*\<^sup>* M N"

text \<open>Sanity check: @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma> = \<rightarrow>\<^sub>\<beta> \<union> \<rightarrow>\<sigma>"}.\<close>

lemma beta_sigma_step_iff_beta_or_sigma:
  "M \<rightarrow>\<beta>\<sigma> N \<longleftrightarrow> M \<rightarrow>\<beta> N \<or> M \<rightarrow>\<sigma> N"
proof
  assume "M \<rightarrow>\<beta>\<sigma> N"
  then show "M \<rightarrow>\<beta> N \<or> M \<rightarrow>\<sigma> N"
    by (induction rule: beta_sigma_step.induct)
       (blast intro: beta_step.intros sigma_step.intros)+
next
  assume "M \<rightarrow>\<beta> N \<or> M \<rightarrow>\<sigma> N"
  then show "M \<rightarrow>\<beta>\<sigma> N"
  proof
    assume "M \<rightarrow>\<beta> N"
    then show ?thesis
      by (induction rule: beta_step.induct)
         (blast intro: beta_sigma_step.intros)+
  next
    assume "M \<rightarrow>\<sigma> N"
    then show ?thesis
      by (induction rule: sigma_step.induct)
         (blast intro: beta_sigma_step.intros)+
  qed
qed

end
