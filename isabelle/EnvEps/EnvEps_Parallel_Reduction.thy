theory EnvEps_Parallel_Reduction
  imports EnvEps_Sigma_Normal_Form_Grammar
begin

text \<open>
  Parallel reduction @{text "\<Rightarrow>\<^sub>p\<^sub>a\<^sub>r"} on @{text "\<sigma>"}-normal forms (docs
  file @{text "docs/enve-parallel-reduction.md"}, thesis Definition 14;
  roadmap item 17). Written @{text "\<Rightarrow>\<^sub>p\<^sub>a\<^sub>r"} (double arrow, ASCII-safe
  name) rather than the docs' @{text "\<Rightarrow>\<^sub>p\<^sub>a\<^sub>r"} to keep it visually distinct
  from the single-arrow relations elsewhere in this development. Although
  the relation is only meaningful between @{text "\<sigma>"}-normal forms (its
  intended domain, per the docs), it is defined here as an ordinary
  inductive predicate on all of @{text trm}.

  \<^bold>\<open>Adjustment to the docs.\<close> The side condition @{text "W \<noteq> Id"} has been
  added to @{text ParVarComp} and to @{text ParBetaClos}; the docs
  (thesis Definition 14) state only "@{text W} is not an environment
  extension" for the former and no condition on @{text W} for the latter.
  Both additions are forced, not restrictive: the docs declare
  @{text "\<Rightarrow>par"} to be defined only between @{text "\<sigma>"}-normal forms, and
  for @{term "Comp (Var x) W"} (respectively @{term "Comp (Lam x U) W"},
  the left argument of @{text ParBetaClos}'s source) to be
  @{text "\<sigma>"}-normal, grammar (2.32)
  (@{text EnvEps_Sigma_Normal_Form_Grammar}) already requires
  @{text "W \<noteq> Id"} -- otherwise @{text IdR} would fire. So on the
  intended domain the conditions hold automatically and the relation is
  unchanged; stating them explicitly is what makes
  @{text par_step_source_normal} below provable, and with it the
  unconditional diamond property.
\<close>

inductive par_step :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<Rightarrow>par" 50) where
  ParVar:
    "Var x \<Rightarrow>par Var x"
| ParId:
    "Id \<Rightarrow>par Id"
| ParLam:
    "U \<Rightarrow>par U' \<Longrightarrow> Lam x U \<Rightarrow>par Lam x U'"
| ParEps:
    "U \<Rightarrow>par U' \<Longrightarrow> Eps U \<Rightarrow>par Eps U'"
| ParApp:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V' \<Longrightarrow> App U V \<Rightarrow>par App U' V'"
| ParExtn:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V' \<Longrightarrow> Ext U x V \<Rightarrow>par Ext U' x V'"
| ParLamComp:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V' \<Longrightarrow> V \<noteq> Id
     \<Longrightarrow> Comp (Lam x U) V \<Rightarrow>par sigma_nf (Comp (Lam x U') V')"
| ParVarComp:
    "W \<Rightarrow>par W' \<Longrightarrow> W \<noteq> Id \<Longrightarrow> (\<nexists>P y Q. W = Ext P y Q)
     \<Longrightarrow> Comp (Var x) W \<Rightarrow>par sigma_nf (Comp (Var x) W')"
| ParBeta:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V'
     \<Longrightarrow> App (Lam x U) V \<Rightarrow>par sigma_nf (Comp U' (Ext V' x Id))"
| ParBetaClos:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V' \<Longrightarrow> W \<Rightarrow>par W' \<Longrightarrow> W \<noteq> Id
     \<Longrightarrow> App (Comp (Lam x U) W) V \<Rightarrow>par sigma_nf (Comp U' (Ext V' x W'))"
| ParCompEps:
    "U \<Rightarrow>par U' \<Longrightarrow> V \<Rightarrow>par V'
     \<Longrightarrow> App (Eps U) V \<Rightarrow>par sigma_nf (Comp U' V')"

abbreviation par_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<Rightarrow>par\<^sup>*" 50) where
  "U \<Rightarrow>par\<^sup>* V \<equiv> par_step\<^sup>*\<^sup>* U V"

end
