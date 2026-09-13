theory EnvEps_Parallel_Reduction_Confluence
  imports EnvEps_Parallel_Reduction_Triangle_Property
    EnvEps_Parallel_Reduction_Reflexivity Diamond_Implies_Confluence
begin

text \<open>
  Confluence of @{text "\<Rightarrow>par"} (docs file
  @{text "docs/enve-parallel-reduction-confluence.md"}, thesis
  Theorem 11; roadmap item 24), from the diamond property
  (@{text "EnvEps_Parallel_Reduction_Triangle_Property.par_step_triangle"})
  via the generic, fully proved
  @{text "Diamond_Implies_Confluence.diamond_implies_confluence"}.

  The triangle property is stated only for @{text "\<sigma>"}-normal
  @{term U}, but that hypothesis is \<^emph>\<open>derivable\<close> from the reduction step
  itself (@{text par_step_source_normal}), so the diamond property below
  -- and hence this theorem -- holds unconditionally on all of
  @{typ trm}, with no domain side condition left to thread through.

  This theory introduces no gap of its own; it inherits only the one in
  @{text par_step_triangle}.
\<close>

lemma par_step_diamond:
  assumes "U \<Rightarrow>par V\<^sub>1" and "U \<Rightarrow>par V\<^sub>2"
  shows "\<exists>W. V\<^sub>1 \<Rightarrow>par W \<and> V\<^sub>2 \<Rightarrow>par W"
proof -
  have "is_sigma_normal U" using assms(1) by (rule par_step_source_normal)
  from par_step_triangle [OF this assms(1)] par_step_triangle [OF this assms(2)]
  show ?thesis by blast
qed

theorem par_step_confluent:
  assumes "U \<Rightarrow>par\<^sup>* V\<^sub>1" and "U \<Rightarrow>par\<^sup>* V\<^sub>2"
  shows "\<exists>W. V\<^sub>1 \<Rightarrow>par\<^sup>* W \<and> V\<^sub>2 \<Rightarrow>par\<^sup>* W"
  using par_step_diamond assms by (rule diamond_implies_confluence)

end
