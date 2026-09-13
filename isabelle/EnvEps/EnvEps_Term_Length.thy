theory EnvEps_Term_Length
  imports EnvEps_Syntax
begin

text \<open>
  The @{text length} termination measure on @{text "lambda_EnvEps"}
  terms (docs file @{text "docs/enve-term-length-measure.md"}, thesis
  Definition 11 / equation (2.20)).

  The thesis states @{text length} takes values in the positive
  integers; here it is defined into @{typ nat} (Isabelle's @{typ nat}
  starts at @{text 0}), and positivity is proved separately below as
  @{text length_pos}.
\<close>

fun length_enve :: "trm \<Rightarrow> nat" where
  "length_enve Id          = 1"
| "length_enve (Var x)     = 1"
| "length_enve (App M N)   = length_enve M + length_enve N + 1"
| "length_enve (Ext M x N) = length_enve M + length_enve N + 1"
| "length_enve (Lam x M)   = 2 * length_enve M"
| "length_enve (Eps M)     = 2 * length_enve M"
| "length_enve (Comp M N)  = length_enve M * (length_enve N + 1)"

lemma length_pos [simp]: "length_enve M > 0"
  by (induction M) auto

end
