theory Diamond_Implies_Confluence
  imports Main
begin

text \<open>
  Generic fact: a relation with the diamond property has a confluent
  reflexive-transitive closure. Fully generic (not specific to any
  calculus in this repository); used to justify the Fact of
  @{text "docs/enve-parallel-reduction-confluence.md"} (roadmap item 24)
  without re-deriving it there. Follows exactly the two-step argument
  given in the docs (Step 1: strip lemma; Step 2: general confluence),
  each by induction peeling the first step of a chain -- i.e.
  @{text converse_rtranclp_induct} -- applied to a universally quantified
  auxiliary statement so the "current" one-step partner can vary freely
  as the induction proceeds.
\<close>

lemma diamond_strip_aux:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes diamond: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> \<exists>w. r y w \<and> r z w"
  shows "r\<^sup>*\<^sup>* x z \<Longrightarrow> \<forall>y. r x y \<longrightarrow> (\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w)"
proof (induction x rule: converse_rtranclp_induct [where b = z])
  case base
  then show ?case by blast
next
  case (step a c)
  \<comment> \<open>Peeled: @{term "r a c"}, @{term "r\<^sup>*\<^sup>* c z"}; IH available for @{term c}.\<close>
  show ?case
  proof (intro allI impI)
    fix y assume "r a y"
    from diamond [OF this \<open>r a c\<close>] obtain x' where x': "r y x'" "r c x'" by blast
    from step.IH [rule_format, OF x'(2)] obtain w where w: "r\<^sup>*\<^sup>* x' w" "r\<^sup>*\<^sup>* z w" by blast
    have "r\<^sup>*\<^sup>* y w" using x'(1) w(1) by (rule converse_rtranclp_into_rtranclp)
    with w(2) show "\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w" by blast
  qed
qed

lemma diamond_strip:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes diamond: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> \<exists>w. r y w \<and> r z w"
    and step1: "r x y" and chain: "r\<^sup>*\<^sup>* x z"
  shows "\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w"
proof -
  have "\<forall>y. r x y \<longrightarrow> (\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w)"
    using diamond chain by (rule diamond_strip_aux)
  then show ?thesis using step1 by blast
qed

lemma diamond_implies_confluence_aux:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes diamond: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> \<exists>w. r y w \<and> r z w"
  shows "r\<^sup>*\<^sup>* x y \<Longrightarrow> \<forall>z. r\<^sup>*\<^sup>* x z \<longrightarrow> (\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w)"
proof (induction x rule: converse_rtranclp_induct [where b = y])
  case base
  then show ?case by blast
next
  case (step a c)
  \<comment> \<open>Peeled: @{term "r a c"}, @{term "r\<^sup>*\<^sup>* c y"}; IH available for @{term c}.\<close>
  show ?case
  proof (intro allI impI)
    fix z assume az: "r\<^sup>*\<^sup>* a z"
    have "\<exists>w. r\<^sup>*\<^sup>* c w \<and> r\<^sup>*\<^sup>* z w"
      using diamond \<open>r a c\<close> az by (rule diamond_strip)
    then obtain w\<^sub>1 where w1: "r\<^sup>*\<^sup>* c w\<^sub>1" "r\<^sup>*\<^sup>* z w\<^sub>1" by blast
    from step.IH [rule_format, OF w1(1)] obtain w where w: "r\<^sup>*\<^sup>* y w" "r\<^sup>*\<^sup>* w\<^sub>1 w" by blast
    have "r\<^sup>*\<^sup>* z w" using w1(2) w(2) by (rule rtranclp_trans)
    with w(1) show "\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w" by blast
  qed
qed

theorem diamond_implies_confluence:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes diamond: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> \<exists>w. r y w \<and> r z w"
    and xy: "r\<^sup>*\<^sup>* x y" and xz: "r\<^sup>*\<^sup>* x z"
  shows "\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w"
proof -
  have "\<forall>z. r\<^sup>*\<^sup>* x z \<longrightarrow> (\<exists>w. r\<^sup>*\<^sup>* y w \<and> r\<^sup>*\<^sup>* z w)"
    using diamond xy by (rule diamond_implies_confluence_aux)
  then show ?thesis using xz by blast
qed

end
