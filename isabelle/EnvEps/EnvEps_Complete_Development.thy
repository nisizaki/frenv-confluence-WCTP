theory EnvEps_Complete_Development
  imports EnvEps_Sigma_Normal_Form
begin

text \<open>
  Complete development @{text cd} on @{text "\<sigma>"}-normal forms (docs file
  @{text "docs/enve-complete-development.md"}, thesis Definition 15,
  equations (2.52)-(2.53), the thesis's postfix @{text "M\<^sup>*"}; roadmap
  item 21). Defined here as a total function on all of @{text trm} (as
  Isabelle's @{command fun} requires), even though it is only meaningful
  -- and only claimed by the docs to compute a @{text "\<sigma>"}-normal form --
  on @{text "\<sigma>"}-normal-form inputs. The @{text Comp} case not covered by
  grammar (2.32) (i.e. @{text M} not @{text Var}-headed or
  @{text Lam}-headed) and the @{text App} "otherwise" case fall back to
  the same recurse-and-@{text sigma_nf} / recurse-only pattern as the
  nearest documented case, which is harmless since those inputs never
  arise when @{text cd} is applied to an actual @{text "\<sigma>"}-normal form.
\<close>

fun cd :: "trm \<Rightarrow> trm" where
  "cd (Var x) = Var x"
| "cd Id = Id"
| "cd (Lam x M) = Lam x (cd M)"
| "cd (Eps M) = Eps (cd M)"
| "cd (Ext M x N) = Ext (cd M) x (cd N)"
| "cd (Comp (Var x) M) = sigma_nf (Comp (Var x) (cd M))"
| "cd (Comp (Lam x M) N) = sigma_nf (Comp (Lam x (cd M)) (cd N))"
| "cd (Comp M N) = sigma_nf (Comp (cd M) (cd N))"
| "cd (App (Lam x M) N) = sigma_nf (Comp (cd M) (Ext (cd N) x Id))"
| "cd (App (Comp (Lam x M) L) N) = sigma_nf (Comp (cd M) (Ext (cd N) x (cd L)))"
| "cd (App (Eps M) N) = sigma_nf (Comp (cd M) (cd N))"
| "cd (App M N) = App (cd M) (cd N)"

end
