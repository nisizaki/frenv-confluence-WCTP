theory EnvEps_FREnv_Translation_Simulation
  imports EnvEps_FREnv_Translation EnvEps_BetaSigma
    "FREnv.FREnv_BetaSigma_Congruence"
begin

text \<open>
  Simulation of @{text "lambda_EnvEps"}'s @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"} by @{text "\<lbrakk>-\<rbrakk>"}
  (docs file @{text "docs/enve-frenv-translation-simulation.md"}, thesis
  Lemma 2; roadmap item 29): every @{text "lambda_EnvEps"} step
  translates to a (possibly zero-step) @{text "lambda_FREnv"} reduction.

  Both calculi call their relation @{text beta_sigma_step} and use the
  same infix syntax, so this theory fixes unambiguous local names:
  @{text "\<rightarrow>E"} for the @{text "lambda_EnvEps"} step relation and
  @{text "\<rightarrow>F"} / @{text "\<rightarrow>F\<^sup>*"} for the @{text "lambda_FREnv"} ones.

  The proof is a case analysis on the nineteen rules of
  @{text "\<rightarrow>E"}. Each translates to exactly one @{text "\<rightarrow>F"} step, using
  the identically-named rule of @{text "lambda_FREnv"} -- except
  @{text CompEps}, whose two sides have the \<^emph>\<open>same\<close> translation (the
  translation of @{term "Comp M N"} is by definition
  @{term "App (Eps \<lbrakk>M\<rbrakk>) \<lbrakk>N\<rbrakk>"}, which is already what
  @{term "App (Eps M) N"} translates to), so it needs zero steps; and the
  eight congruence rules, which transport the induction hypothesis
  through a constructor with @{text FREnv_BetaSigma_Congruence}.

  The two @{text Comp} congruence rules are the only ones where the
  translation changes the shape: @{term "Comp A B"} becomes
  @{term "App (Eps \<lbrakk>A\<rbrakk>) \<lbrakk>B\<rbrakk>"}, so @{text CompL} lifts through
  @{text EnvAbst} and then @{text AppL}, and @{text CompR} through
  @{text AppR}.
\<close>

abbreviation estep :: "EnvEps_Syntax.trm \<Rightarrow> EnvEps_Syntax.trm \<Rightarrow> bool" (infix "\<rightarrow>E" 50)
  where "M \<rightarrow>E N \<equiv> EnvEps_BetaSigma.beta_sigma_step M N"

abbreviation fstep :: "FREnv_Syntax.trm \<Rightarrow> FREnv_Syntax.trm \<Rightarrow> bool" (infix "\<rightarrow>F" 50)
  where "M \<rightarrow>F N \<equiv> FREnv_BetaSigma.beta_sigma_step M N"

abbreviation fsteps :: "FREnv_Syntax.trm \<Rightarrow> FREnv_Syntax.trm \<Rightarrow> bool" (infix "\<rightarrow>F\<^sup>*" 50)
  where "M \<rightarrow>F\<^sup>* N \<equiv> FREnv_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M N"

theorem translate_simulates_beta_sigma_step:
  assumes "M \<rightarrow>E N"
  shows "\<lbrakk>M\<rbrakk> \<rightarrow>F\<^sup>* \<lbrakk>N\<rbrakk>"
  using assms
proof (induction rule: EnvEps_BetaSigma.beta_sigma_step.induct)
  case (Beta x A B)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.Beta)
next
  case (BetaClos x A L B)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.BetaClos)
next
  case (CompEps A B)
  \<comment> \<open>Both sides have the same translation; zero steps.\<close>
  show ?case by auto
next
  case (Assoc A B C)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.Assoc)
next
  case (IdL A)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.IdL)
next
  case (IdR A)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.IdR)
next
  case (DExtn L x A B)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.DExtn)
next
  case (VarRef x A B)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.VarRef)
next
  case (VarSkip x y A B)
  then show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.VarSkip)
next
  case (DApp A B C)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.DApp)
next
  case (EpsEps A B)
  show ?case by (auto intro: FREnv_BetaSigma.beta_sigma_step.EpsEps)
next
  case (AppL A A' B)
  then show ?case by auto
next
  case (AppR B B' A)
  then show ?case by auto
next
  case (Lam A A' x)
  then show ?case by auto
next
  case (ExtnL A A' x B)
  then show ?case by auto
next
  case (ExtnR B B' A x)
  then show ?case by auto
next
  case (CompL A A' B)
  \<comment> \<open>@{term "Comp A B"} translates to @{term "App (Eps \<lbrakk>A\<rbrakk>) \<lbrakk>B\<rbrakk>"}, so a step
      on the left component lifts through @{text Eps} and then
      @{text AppL}.\<close>
  then show ?case by auto
next
  case (CompR B B' A)
  then show ?case by auto
next
  case (Eop A A')
  then show ?case by auto
qed

text \<open>The multi-step version, by chain-length induction.\<close>

lemma translate_simulates_beta_sigma_steps:
  assumes "EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M N"
  shows "\<lbrakk>M\<rbrakk> \<rightarrow>F\<^sup>* \<lbrakk>N\<rbrakk>"
  using assms
  by (induction rule: rtranclp.induct)
     (auto dest: translate_simulates_beta_sigma_step intro: rtranclp_trans)

end
