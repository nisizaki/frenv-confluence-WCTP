theory Newmans_Lemma
  imports "Abstract-Rewriting.Abstract_Rewriting"
begin

text \<open>
  Newman's Lemma (1942): a terminating, locally confluent abstract
  rewriting relation is confluent. This is completely generic (not
  specific to any of the calculi in this repository) and is used to
  justify Fact 3 of @{text "docs/enve-sigma-reduction-confluence.md"}
  (roadmap item 12) without re-deriving it from scratch.

  Rather than re-proving Newman's Lemma by hand, this theory reuses the
  already machine-checked @{text Newman} theorem of the vendored AFP
  entry @{text "../vendor/Abstract-Rewriting/"}
  (@{text "Abstract_Rewriting.Newman: SN r \<Longrightarrow> WCR r \<Longrightarrow> CR r"}), which
  works with set-valued relations @{typ "'a rel"}. The lemma below is a
  thin wrapper translating to and from the curried, predicate-valued
  relations (@{typ "'a \<Rightarrow> 'a \<Rightarrow> bool"} with @{text "\<^sup>*\<^sup>*"}) used
  throughout this repository's own reduction relations.
\<close>

lemma newmans_lemma:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes wf: "wf {(y, x). r x y}"
    and lc: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> \<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u"
    and xy: "r\<^sup>*\<^sup>* x y"
    and xz: "r\<^sup>*\<^sup>* x z"
  shows "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u"
proof -
  define R :: "'a rel" where "R = {(a, b). r a b}"
  have SN: "SN R"
    unfolding SN_iff_wf
  proof -
    have "R\<inverse> = {(y, x). r x y}" by (auto simp: R_def)
    then show "wf (R\<inverse>)" using wf by simp
  qed
  have WCR: "WCR R"
    unfolding WCR_on_def
  proof (intro ballI allI impI)
    fix x y z
    assume "(x, y) \<in> R \<and> (x, z) \<in> R"
    then have "r x y" "r x z" by (auto simp: R_def)
    then obtain u where "r\<^sup>*\<^sup>* y u" "r\<^sup>*\<^sup>* z u" using lc by blast
    then have "(y, u) \<in> R\<^sup>*" "(z, u) \<in> R\<^sup>*"
      by (simp_all add: rtranclp_rtrancl_eq R_def)
    then show "(y, z) \<in> R\<^sup>\<down>" by (rule joinI)
  qed
  from Newman [OF SN WCR] have CR: "CR R" .
  have "(x, y) \<in> R\<^sup>*" "(x, z) \<in> R\<^sup>*"
    using xy xz by (simp_all add: rtranclp_rtrancl_eq R_def)
  with CR have "(y, z) \<in> R\<^sup>\<down>" unfolding CR_on_def by blast
  then obtain u where "(y, u) \<in> R\<^sup>*" "(z, u) \<in> R\<^sup>*" by (rule joinE)
  then have "r\<^sup>*\<^sup>* y u" "r\<^sup>*\<^sup>* z u"
    by (simp_all add: rtranclp_rtrancl_eq R_def)
  then show ?thesis by blast
qed

end
