theory EnvEps_FREnv_Translation_Lifting
  imports EnvEps_FREnv_Translation_Simulation EnvEps_BetaSigma_Congruence
    EnvEps_FREnv_Translation_Inversion
begin

text \<open>
  Single-step lifting lemma (docs file
  @{text "docs/enve-frenv-translation-lifting.md"}, thesis Lemma 3;
  roadmap item 30): a single @{text "lambda_FREnv"}-side
  @{text "\<rightarrow>\<^sub>\<beta>\<^sub>\<sigma>"}-step out of @{text "\<lbrakk>M\<rbrakk>"} is matched by an explicit,
  purely @{text "lambda_EnvEps"}-side reduction of @{text M} -- no
  confluence or joinability fact needed, per the docs' own emphasis.

  The proof is by strong induction on the size of the @{text "lambda_FREnv"}
  source term (not plain rule induction: the two congruence cases
  @{text AppL}/@{text AppR} need to recurse into an arbitrarily deep
  @{text "lambda_EnvEps"}-side @{text Comp} preimage, since translation
  identifies @{term "Comp P Q"} with @{term "App (Eps P) Q"}), case-split
  on the rule of @{text "FREnv.beta_sigma_step"} used. Every
  @{text "lambda_FREnv"}-headed @{text App} shape has two possible
  @{text "lambda_EnvEps"} preimages (a literal @{text App}, or a
  @{text Comp} whose translation coincides with it), handled uniformly via
  the inversion lemmas of @{text EnvEps_FREnv_Translation_Inversion}.

  \<^bold>\<open>Fixed foundational mismatch.\<close> The @{text BetaClos} case has two
  preimage shapes for @{term M}: @{text "App (Comp (Lam x M1) M2) M3"} and
  @{text "App (App (Eps (Lam x M1)) M2) M3"} (both translate to the same
  @{text "lambda_FREnv"} term, since translation identifies
  @{text "Comp P Q"} with @{text "App (Eps P) Q"}). An earlier version of
  @{text "EnvEps_BetaSigma.BetaClos"} (roadmap item 15) fired only on the
  second, literal @{text "lambda_FREnv"}-shaped pattern -- a mistranscription
  traced to the thesis's own Definition 5, which states
  @{text "((\<lambda>x.M) \<circ> L)N \<rightarrow> M \<circ> ((N/x)\<cdot>L)"} (@{text Comp}-headed), not the
  @{text "App"}-@{text "Eps"}-headed pattern that @{text "lambda_FREnv"}'s
  own (structurally different) @{text BetaClos} rule uses. Now that
  @{text EnvEps_BetaSigma.BetaClos} matches the thesis literally, the first
  preimage fires @{text BetaClos} directly and the second needs one
  @{text "Comp\<^sub>\<epsilon>"} step (lifted through @{text AppL}) first to expose the
  @{text Comp}-headed left argument; both are proved in full below, along
  with every other case.
\<close>

abbreviation esteps :: "EnvEps_Syntax.trm \<Rightarrow> EnvEps_Syntax.trm \<Rightarrow> bool" (infix "\<rightarrow>E\<^sup>*" 50)
  where "M \<rightarrow>E\<^sup>* N \<equiv> EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M N"

lemma frenv_Eps_step_inv:
  "FREnv_Syntax.Eps P \<rightarrow>F A' \<Longrightarrow> \<exists>P'. A' = FREnv_Syntax.Eps P' \<and> P \<rightarrow>F P'"
  by (cases rule: FREnv_BetaSigma.beta_sigma_step.cases) auto

lemma compeps_prefix:
  assumes "EnvEps_Syntax.Comp P Q \<rightarrow>E\<^sup>* Y"
  shows "EnvEps_Syntax.App (EnvEps_Syntax.Eps P) Q \<rightarrow>E\<^sup>* Y"
proof -
  have "EnvEps_Syntax.App (EnvEps_Syntax.Eps P) Q \<rightarrow>E\<^sup>* EnvEps_Syntax.Comp P Q"
    by (auto intro: EnvEps_BetaSigma.beta_sigma_step.CompEps)
  also note assms
  finally show ?thesis .
qed

lemma translate_single_step_lifting_aux:
  assumes "a \<rightarrow>F b" and "a = \<lbrakk>M\<rbrakk>"
  shows "\<exists>N L. \<lbrakk>N\<rbrakk> = b \<and> N \<rightarrow>E\<^sup>* L \<and> M \<rightarrow>E\<^sup>* L"
  using assms
proof (induction "size a" arbitrary: a b M rule: less_induct)
  case less
  note step = less.prems(1) and Meq = less.prems(2)
  from step Meq show "\<exists>N L. \<lbrakk>N\<rbrakk> = b \<and> N \<rightarrow>E\<^sup>* L \<and> M \<rightarrow>E\<^sup>* L"
  proof (cases rule: FREnv_BetaSigma.beta_sigma_step.cases)
    case (Beta x A B)
    from translate_App_inv [OF Meq [unfolded Beta(1), symmetric]]
    obtain M1 M2 where "M = EnvEps_Syntax.App M1 M2 \<and> FREnv_Syntax.Lam x A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>
                       \<or> M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Lam x A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
      by blast
    then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.App M1 M2"
        and M1eq: "FREnv_Syntax.Lam x A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by auto
    from translate_Lam_inv [OF M1eq [symmetric]]
    obtain M1' where M1shape: "M1 = EnvEps_Syntax.Lam x M1'" and Aeq: "A = \<lbrakk>M1'\<rbrakk>" by blast
    define L where "L = EnvEps_Syntax.Comp M1' (EnvEps_Syntax.Ext M2 x EnvEps_Syntax.Id)"
    have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps A) (FREnv_Syntax.Ext B x FREnv_Syntax.Id)"
      unfolding L_def by (simp add: Aeq M2eq)
    have "M \<rightarrow>E\<^sup>* L"
      unfolding Mshape M1shape L_def
      by (auto intro: EnvEps_BetaSigma.beta_sigma_step.Beta)
    with Leq show ?thesis unfolding Beta(2) by blast
  next
    case (BetaClos x A W B)
    from translate_App_inv [OF Meq [unfolded BetaClos(1), symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2
              \<and> FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Lam x A)) W = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2
              \<and> FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Lam x A)) W = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.App M1 M2"
        and M1eq: "FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Lam x A)) W = \<lbrakk>M1\<rbrakk>"
        and M2eq: "B = \<lbrakk>M2\<rbrakk>"
      by auto
    from translate_AppEps_inv [OF M1eq [symmetric]]
    have "(\<exists>M1a M1b. M1 = EnvEps_Syntax.Comp M1a M1b \<and> FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk> \<and> W = \<lbrakk>M1b\<rbrakk>)
        \<or> (\<exists>M1a M1b. M1 = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) M1b \<and> FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk> \<and> W = \<lbrakk>M1b\<rbrakk>)"
      by blast
    then show ?thesis
    proof
      assume "\<exists>M1a M1b. M1 = EnvEps_Syntax.Comp M1a M1b \<and> FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk> \<and> W = \<lbrakk>M1b\<rbrakk>"
      then obtain M1a M1b where M1shape: "M1 = EnvEps_Syntax.Comp M1a M1b"
          and M1aeq: "FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk>" and Weq: "W = \<lbrakk>M1b\<rbrakk>" by blast
      from translate_Lam_inv [OF M1aeq [symmetric]]
      obtain M1a' where M1ashape: "M1a = EnvEps_Syntax.Lam x M1a'" and Aeq: "A = \<lbrakk>M1a'\<rbrakk>" by blast
      define L where "L = EnvEps_Syntax.Comp M1a' (EnvEps_Syntax.Ext M2 x M1b)"
      have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps A) (FREnv_Syntax.Ext B x W)"
        unfolding L_def by (simp add: Aeq M2eq Weq)
      have "M \<rightarrow>E\<^sup>* L"
        unfolding Mshape M1shape M1ashape L_def
        by (auto intro: EnvEps_BetaSigma.beta_sigma_step.BetaClos)
      with Leq show ?thesis unfolding BetaClos(2) by blast
    next
      assume "\<exists>M1a M1b. M1 = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) M1b \<and> FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk> \<and> W = \<lbrakk>M1b\<rbrakk>"
      then obtain M1a M1b where M1shape: "M1 = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) M1b"
          and M1aeq: "FREnv_Syntax.Lam x A = \<lbrakk>M1a\<rbrakk>" and Weq: "W = \<lbrakk>M1b\<rbrakk>" by blast
      from translate_Lam_inv [OF M1aeq [symmetric]]
      obtain M1a' where M1ashape: "M1a = EnvEps_Syntax.Lam x M1a'" and Aeq: "A = \<lbrakk>M1a'\<rbrakk>" by blast
      define L where "L = EnvEps_Syntax.Comp M1a' (EnvEps_Syntax.Ext M2 x M1b)"
      have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps A) (FREnv_Syntax.Ext B x W)"
        unfolding L_def by (simp add: Aeq M2eq Weq)
      \<comment> \<open>With @{text BetaClos} now (correctly) firing only on the literal
          @{text "App (Comp (Lam x M) L) N"} shape (matching the thesis's
          own Definition 5, not the @{text "lambda_FREnv"}-shaped
          @{text "App (App (Eps (Lam x M)) L) N"} this rule used to have),
          this preimage needs one @{text "Comp\<^sub>\<epsilon>"} step (lifted through
          @{text AppL}) to expose the @{text Comp}-headed left argument
          before @{text BetaClos} can fire.\<close>
      have step1a: "EnvEps_Syntax.App (EnvEps_Syntax.Eps (EnvEps_Syntax.Lam x M1a')) M1b
          \<rightarrow>E EnvEps_Syntax.Comp (EnvEps_Syntax.Lam x M1a') M1b"
        by (rule EnvEps_BetaSigma.beta_sigma_step.CompEps)
      have step1: "M \<rightarrow>E EnvEps_Syntax.App (EnvEps_Syntax.Comp (EnvEps_Syntax.Lam x M1a') M1b) M2"
        unfolding Mshape M1shape M1ashape
        using step1a by (rule EnvEps_BetaSigma.beta_sigma_step.AppL)
      have "M \<rightarrow>E\<^sup>* EnvEps_Syntax.App (EnvEps_Syntax.Comp (EnvEps_Syntax.Lam x M1a') M1b) M2"
        using step1 by (rule r_into_rtranclp)
      also have "EnvEps_Syntax.App (EnvEps_Syntax.Comp (EnvEps_Syntax.Lam x M1a') M1b) M2 \<rightarrow>E\<^sup>* L"
        unfolding L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.BetaClos)
      finally have "M \<rightarrow>E\<^sup>* L" .
      with Leq show ?thesis unfolding BetaClos(2) by blast
    qed
  next
    case (Assoc A B C)
    from translate_AppEps_inv [OF Meq [unfolded Assoc(1), symmetric]]
    have "(\<exists>M1 M0. M = EnvEps_Syntax.Comp M1 M0
              \<and> FREnv_Syntax.App (FREnv_Syntax.Eps A) B = \<lbrakk>M1\<rbrakk> \<and> C = \<lbrakk>M0\<rbrakk>)
        \<or> (\<exists>M1 M0. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M0
              \<and> FREnv_Syntax.App (FREnv_Syntax.Eps A) B = \<lbrakk>M1\<rbrakk> \<and> C = \<lbrakk>M0\<rbrakk>)"
      by blast
    then obtain M1 M0 M0eq outerCompEps
      where Mouter: "M = EnvEps_Syntax.Comp M1 M0 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M0 \<and> outerCompEps)"
        and M1eq: "FREnv_Syntax.App (FREnv_Syntax.Eps A) B = \<lbrakk>M1\<rbrakk>" and M0eq: "C = \<lbrakk>M0\<rbrakk>"
      by (metis (full_types))
    from translate_AppEps_inv [OF M1eq [symmetric]]
    obtain M1a M1b innerCompEps
      where M1inner: "M1 = EnvEps_Syntax.Comp M1a M1b \<or> (M1 = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) M1b \<and> innerCompEps)"
        and M1aeq: "A = \<lbrakk>M1a\<rbrakk>" and M1beq: "B = \<lbrakk>M1b\<rbrakk>"
      by (metis (full_types))
    define L where "L = EnvEps_Syntax.Comp M1a (EnvEps_Syntax.Comp M1b M0)"
    have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps A) (FREnv_Syntax.App (FREnv_Syntax.Eps B) C)"
      unfolding L_def by (simp add: M1aeq M1beq M0eq)
    have M1_to_CompM1aM1b: "M1 \<rightarrow>E\<^sup>* EnvEps_Syntax.Comp M1a M1b"
      using M1inner by (auto intro: EnvEps_BetaSigma.beta_sigma_step.CompEps)
    have M_to_CompM1M0: "M \<rightarrow>E\<^sup>* EnvEps_Syntax.Comp M1 M0"
      using Mouter by (auto intro: EnvEps_BetaSigma.beta_sigma_step.CompEps)
    have "EnvEps_Syntax.Comp M1 M0 \<rightarrow>E\<^sup>* EnvEps_Syntax.Comp (EnvEps_Syntax.Comp M1a M1b) M0"
      using M1_to_CompM1aM1b by (auto intro: bs_steps_CompL)
    also have "EnvEps_Syntax.Comp (EnvEps_Syntax.Comp M1a M1b) M0 \<rightarrow>E\<^sup>* L"
      unfolding L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.Assoc)
    finally have "EnvEps_Syntax.Comp M1 M0 \<rightarrow>E\<^sup>* L" .
    with M_to_CompM1M0 have "M \<rightarrow>E\<^sup>* L" by (rule rtranclp_trans)
    with Leq show ?thesis unfolding Assoc(2) by blast
  next
    case IdL
    from translate_AppEps_inv [OF Meq [unfolded IdL, symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Id = \<lbrakk>M1\<rbrakk> \<and> b = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> FREnv_Syntax.Id = \<lbrakk>M1\<rbrakk> \<and> b = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "FREnv_Syntax.Id = \<lbrakk>M1\<rbrakk>" and M2eq: "b = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Id_inv [OF M1eq [symmetric]] have M1shape: "M1 = EnvEps_Syntax.Id" .
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* M2"
      unfolding M1shape by (auto intro: EnvEps_BetaSigma.beta_sigma_step.IdL)
    have "M \<rightarrow>E\<^sup>* M2" using Mouter core by (auto intro: compeps_prefix)
    with M2eq show ?thesis by blast
  next
    case IdR
    from translate_AppEps_inv [OF Meq [unfolded IdR, symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> b = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Id = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> b = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Id = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "b = \<lbrakk>M1\<rbrakk>" and M2eq: "FREnv_Syntax.Id = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Id_inv [OF M2eq [symmetric]] have M2shape: "M2 = EnvEps_Syntax.Id" .
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* M1"
      unfolding M2shape by (auto intro: EnvEps_BetaSigma.beta_sigma_step.IdR)
    have "M \<rightarrow>E\<^sup>* M1" using Mouter core by (auto intro: compeps_prefix)
    with M1eq show ?thesis by blast
  next
    case (DExtn P x A B)
    from translate_AppEps_inv [OF Meq [unfolded DExtn(1), symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Ext P x A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> FREnv_Syntax.Ext P x A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "FREnv_Syntax.Ext P x A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Ext_inv [OF M1eq [symmetric]]
    obtain M1a M1b where M1shape: "M1 = EnvEps_Syntax.Ext M1a x M1b" and Peq: "P = \<lbrakk>M1a\<rbrakk>" and Aeq: "A = \<lbrakk>M1b\<rbrakk>" by blast
    define L where "L = EnvEps_Syntax.Ext (EnvEps_Syntax.Comp M1a M2) x (EnvEps_Syntax.Comp M1b M2)"
    have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.Ext (FREnv_Syntax.App (FREnv_Syntax.Eps P) B) x (FREnv_Syntax.App (FREnv_Syntax.Eps A) B)"
      unfolding L_def by (simp add: Peq Aeq M2eq)
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* L"
      unfolding M1shape L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.DExtn)
    have "M \<rightarrow>E\<^sup>* L" using Mouter core by (auto intro: compeps_prefix)
    with Leq show ?thesis unfolding DExtn(2) by blast
  next
    case (VarRef x B)
    from translate_AppEps_inv [OF Meq [unfolded VarRef, symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Var x = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Ext b x B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> FREnv_Syntax.Var x = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Ext b x B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "FREnv_Syntax.Var x = \<lbrakk>M1\<rbrakk>" and M2eq: "FREnv_Syntax.Ext b x B = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Var_inv [OF M1eq [symmetric]] have M1shape: "M1 = EnvEps_Syntax.Var x" .
    from translate_Ext_inv [OF M2eq [symmetric]]
    obtain M2a M2b where M2shape: "M2 = EnvEps_Syntax.Ext M2a x M2b" and Aeq: "b = \<lbrakk>M2a\<rbrakk>" and Beq: "B = \<lbrakk>M2b\<rbrakk>" by blast
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* M2a"
      unfolding M1shape M2shape by (auto intro: EnvEps_BetaSigma.beta_sigma_step.VarRef)
    have "M \<rightarrow>E\<^sup>* M2a" using Mouter core by (auto intro: compeps_prefix)
    with Aeq show ?thesis by blast
  next
    case (VarSkip x y A B)
    have xy: "x \<noteq> y"
      and Msrc: "a = FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Var y)) (FREnv_Syntax.Ext A x B)"
      and Mtgt: "b = FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Var y)) B"
      using VarSkip by simp_all
    from translate_AppEps_inv [OF Meq [unfolded Msrc, symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Var y = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Ext A x B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> FREnv_Syntax.Var y = \<lbrakk>M1\<rbrakk> \<and> FREnv_Syntax.Ext A x B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "FREnv_Syntax.Var y = \<lbrakk>M1\<rbrakk>" and M2eq: "FREnv_Syntax.Ext A x B = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Var_inv [OF M1eq [symmetric]] have M1shape: "M1 = EnvEps_Syntax.Var y" .
    from translate_Ext_inv [OF M2eq [symmetric]]
    obtain M2a M2b where M2shape: "M2 = EnvEps_Syntax.Ext M2a x M2b" and Aeq: "A = \<lbrakk>M2a\<rbrakk>" and Beq: "B = \<lbrakk>M2b\<rbrakk>" by blast
    define L where "L = EnvEps_Syntax.Comp (EnvEps_Syntax.Var y) M2b"
    have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.Eps (FREnv_Syntax.Var y)) B"
      unfolding L_def by (simp add: Beq)
    have yx: "y \<noteq> x" using xy by (rule not_sym)
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* L"
      unfolding M1shape M2shape L_def
      by (auto intro: EnvEps_BetaSigma.beta_sigma_step.VarSkip [OF yx])
    have "M \<rightarrow>E\<^sup>* L" using Mouter core by (auto intro: compeps_prefix)
    with Leq show ?thesis unfolding Mtgt by blast
  next
    case (DApp A B C)
    from translate_AppEps_inv [OF Meq [unfolded DApp(1), symmetric]]
    have "(\<exists>M1 M0. M = EnvEps_Syntax.Comp M1 M0
              \<and> FREnv_Syntax.App A B = \<lbrakk>M1\<rbrakk> \<and> C = \<lbrakk>M0\<rbrakk>)
        \<or> (\<exists>M1 M0. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M0
              \<and> FREnv_Syntax.App A B = \<lbrakk>M1\<rbrakk> \<and> C = \<lbrakk>M0\<rbrakk>)"
      by blast
    then obtain M1 M0 outerCompEps
      where Mouter: "M = EnvEps_Syntax.Comp M1 M0 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M0 \<and> outerCompEps)"
        and M1eq: "FREnv_Syntax.App A B = \<lbrakk>M1\<rbrakk>" and M0eq: "C = \<lbrakk>M0\<rbrakk>"
      by (metis (full_types))
    from translate_App_inv [OF M1eq [symmetric]]
    have "(\<exists>M1a M1b. M1 = EnvEps_Syntax.App M1a M1b \<and> A = \<lbrakk>M1a\<rbrakk> \<and> B = \<lbrakk>M1b\<rbrakk>)
        \<or> (\<exists>M1a M1b. M1 = EnvEps_Syntax.Comp M1a M1b \<and> A = FREnv_Syntax.Eps \<lbrakk>M1a\<rbrakk> \<and> B = \<lbrakk>M1b\<rbrakk>)"
      by blast
    then show ?thesis
    proof
      assume "\<exists>M1a M1b. M1 = EnvEps_Syntax.App M1a M1b \<and> A = \<lbrakk>M1a\<rbrakk> \<and> B = \<lbrakk>M1b\<rbrakk>"
      then obtain M1a M1b where M1shape: "M1 = EnvEps_Syntax.App M1a M1b"
          and Aeq: "A = \<lbrakk>M1a\<rbrakk>" and Beq: "B = \<lbrakk>M1b\<rbrakk>" by blast
      define L where "L = EnvEps_Syntax.App (EnvEps_Syntax.Comp M1a M0) (EnvEps_Syntax.Comp M1b M0)"
      have Leq: "\<lbrakk>L\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.App (FREnv_Syntax.Eps A) C) (FREnv_Syntax.App (FREnv_Syntax.Eps B) C)"
        unfolding L_def by (simp add: Aeq Beq M0eq)
      have core: "EnvEps_Syntax.Comp M1 M0 \<rightarrow>E\<^sup>* L"
        unfolding M1shape L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.DApp)
      have "M \<rightarrow>E\<^sup>* L" using Mouter core by (auto intro: compeps_prefix)
      with Leq show ?thesis unfolding DApp(2) by blast
    next
      assume "\<exists>M1a M1b. M1 = EnvEps_Syntax.Comp M1a M1b \<and> A = FREnv_Syntax.Eps \<lbrakk>M1a\<rbrakk> \<and> B = \<lbrakk>M1b\<rbrakk>"
      then obtain M1a M1b where M1shape: "M1 = EnvEps_Syntax.Comp M1a M1b"
          and Aeq: "A = FREnv_Syntax.Eps \<lbrakk>M1a\<rbrakk>" and Beq: "B = \<lbrakk>M1b\<rbrakk>" by blast
      define N where "N = EnvEps_Syntax.App (EnvEps_Syntax.Comp (EnvEps_Syntax.Eps M1a) M0) (EnvEps_Syntax.Comp M1b M0)"
      define L where "L = EnvEps_Syntax.Comp M1a (EnvEps_Syntax.Comp M1b M0)"
      have Neq: "\<lbrakk>N\<rbrakk> = FREnv_Syntax.App (FREnv_Syntax.App (FREnv_Syntax.Eps A) C) (FREnv_Syntax.App (FREnv_Syntax.Eps B) C)"
        unfolding N_def by (simp add: Aeq Beq M0eq)
      have NtoMid: "N \<rightarrow>E\<^sup>* EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) (EnvEps_Syntax.Comp M1b M0)"
        unfolding N_def by (auto intro: bs_steps_AppL EnvEps_BetaSigma.beta_sigma_step.EpsEps)
      have MidtoL: "EnvEps_Syntax.App (EnvEps_Syntax.Eps M1a) (EnvEps_Syntax.Comp M1b M0) \<rightarrow>E\<^sup>* L"
        unfolding L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.CompEps)
      note NtoL = rtranclp_trans [OF NtoMid MidtoL]
      have Mto: "M \<rightarrow>E\<^sup>* EnvEps_Syntax.Comp (EnvEps_Syntax.Comp M1a M1b) M0"
        using Mouter unfolding M1shape by (auto intro: EnvEps_BetaSigma.beta_sigma_step.CompEps)
      have MidtoL2: "EnvEps_Syntax.Comp (EnvEps_Syntax.Comp M1a M1b) M0 \<rightarrow>E\<^sup>* L"
        unfolding L_def by (auto intro: EnvEps_BetaSigma.beta_sigma_step.Assoc)
      note MtoL = rtranclp_trans [OF Mto MidtoL2]
      with Neq NtoL show ?thesis unfolding DApp(2) by blast
    qed
  next
    case (EpsEps A B)
    from translate_AppEps_inv [OF Meq [unfolded EpsEps(1), symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> FREnv_Syntax.Eps A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> FREnv_Syntax.Eps A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then obtain M1 M2 outer where Mouter: "M = EnvEps_Syntax.Comp M1 M2 \<or> (M = EnvEps_Syntax.App (EnvEps_Syntax.Eps M1) M2 \<and> outer)"
        and M1eq: "FREnv_Syntax.Eps A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>"
      by (metis (full_types))
    from translate_Eps_inv [OF M1eq [symmetric]]
    obtain M1' where M1shape: "M1 = EnvEps_Syntax.Eps M1'" and Aeq: "A = \<lbrakk>M1'\<rbrakk>" by blast
    have core: "EnvEps_Syntax.Comp M1 M2 \<rightarrow>E\<^sup>* EnvEps_Syntax.Eps M1'"
      unfolding M1shape by (auto intro: EnvEps_BetaSigma.beta_sigma_step.EpsEps)
    have "M \<rightarrow>E\<^sup>* EnvEps_Syntax.Eps M1'" using Mouter core by (auto intro: compeps_prefix)
    moreover have "\<lbrakk>EnvEps_Syntax.Eps M1'\<rbrakk> = FREnv_Syntax.Eps A" by (simp add: Aeq)
    ultimately show ?thesis unfolding EpsEps(2) by blast
  next
    case (AppL A A' B)
    from translate_App_inv [OF Meq [unfolded AppL(1), symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then show ?thesis
    proof
      assume "\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
      then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.App M1 M2"
          and M1eq: "A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
      have lt: "size A < size a" unfolding AppL(1) by simp
      from less.hyps [OF lt AppL(3) M1eq] obtain N1 L1
        where N1eq: "\<lbrakk>N1\<rbrakk> = A'" and N1L1: "N1 \<rightarrow>E\<^sup>* L1" and M1L1: "M1 \<rightarrow>E\<^sup>* L1" by blast
      define N where "N = EnvEps_Syntax.App N1 M2"
      define L where "L = EnvEps_Syntax.App L1 M2"
      have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.App A' B" unfolding N_def by (simp add: N1eq M2eq)
      moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N1L1 by (rule bs_steps_AppL)
      moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M1L1 by (rule bs_steps_AppL)
      ultimately show ?thesis unfolding AppL(2) by blast
    next
      assume "\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
      then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.Comp M1 M2"
          and M1eq: "A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
      from AppL(3) [unfolded M1eq] frenv_Eps_step_inv
      obtain P' where A'eq: "A' = FREnv_Syntax.Eps P'" and stepP: "\<lbrakk>M1\<rbrakk> \<rightarrow>F P'" by blast
      have lt: "size \<lbrakk>M1\<rbrakk> < size a" unfolding AppL(1) M1eq by simp
      from less.hyps [OF lt stepP refl] obtain N1 L1
        where N1eq: "\<lbrakk>N1\<rbrakk> = P'" and N1L1: "N1 \<rightarrow>E\<^sup>* L1" and M1L1: "M1 \<rightarrow>E\<^sup>* L1" by blast
      define N where "N = EnvEps_Syntax.Comp N1 M2"
      define L where "L = EnvEps_Syntax.Comp L1 M2"
      have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.App A' B" unfolding N_def A'eq by (simp add: N1eq M2eq)
      moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N1L1 by (rule bs_steps_CompL)
      moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M1L1 by (rule bs_steps_CompL)
      ultimately show ?thesis unfolding AppL(2) by blast
    qed
  next
    case (AppR B B' A)
    from translate_App_inv [OF Meq [unfolded AppR(1), symmetric]]
    have "(\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)
        \<or> (\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>)"
      by blast
    then show ?thesis
    proof
      assume "\<exists>M1 M2. M = EnvEps_Syntax.App M1 M2 \<and> A = \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
      then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.App M1 M2"
          and M1eq: "A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
      have lt: "size B < size a" unfolding AppR(1) by simp
      from less.hyps [OF lt AppR(3) M2eq] obtain N2 L2
        where N2eq: "\<lbrakk>N2\<rbrakk> = B'" and N2L2: "N2 \<rightarrow>E\<^sup>* L2" and M2L2: "M2 \<rightarrow>E\<^sup>* L2" by blast
      define N where "N = EnvEps_Syntax.App M1 N2"
      define L where "L = EnvEps_Syntax.App M1 L2"
      have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.App A B'" unfolding N_def by (simp add: N2eq M1eq)
      moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N2L2 by (rule bs_steps_AppR)
      moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M2L2 by (rule bs_steps_AppR)
      ultimately show ?thesis unfolding AppR(2) by blast
    next
      assume "\<exists>M1 M2. M = EnvEps_Syntax.Comp M1 M2 \<and> A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk> \<and> B = \<lbrakk>M2\<rbrakk>"
      then obtain M1 M2 where Mshape: "M = EnvEps_Syntax.Comp M1 M2"
          and M1eq: "A = FREnv_Syntax.Eps \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
      have lt: "size B < size a" unfolding AppR(1) by simp
      from less.hyps [OF lt AppR(3) M2eq] obtain N2 L2
        where N2eq: "\<lbrakk>N2\<rbrakk> = B'" and N2L2: "N2 \<rightarrow>E\<^sup>* L2" and M2L2: "M2 \<rightarrow>E\<^sup>* L2" by blast
      define N where "N = EnvEps_Syntax.Comp M1 N2"
      define L where "L = EnvEps_Syntax.Comp M1 L2"
      have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.App A B'" unfolding N_def M1eq by (simp add: N2eq)
      moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N2L2 by (rule bs_steps_CompR)
      moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M2L2 by (rule bs_steps_CompR)
      ultimately show ?thesis unfolding AppR(2) by blast
    qed
  next
    case (Lam A A' x)
    from translate_Lam_inv [OF Meq [unfolded Lam(1), symmetric]]
    obtain M1 where Mshape: "M = EnvEps_Syntax.Lam x M1" and M1eq: "A = \<lbrakk>M1\<rbrakk>" by blast
    have lt: "size A < size a" unfolding Lam(1) by simp
    from less.hyps [OF lt Lam(3) M1eq] obtain N1 L1
      where N1eq: "\<lbrakk>N1\<rbrakk> = A'" and N1L1: "N1 \<rightarrow>E\<^sup>* L1" and M1L1: "M1 \<rightarrow>E\<^sup>* L1" by blast
    define N where "N = EnvEps_Syntax.Lam x N1"
    define L where "L = EnvEps_Syntax.Lam x L1"
    have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.Lam x A'" unfolding N_def by (simp add: N1eq)
    moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N1L1 by (rule bs_steps_Lam)
    moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M1L1 by (rule bs_steps_Lam)
    ultimately show ?thesis unfolding Lam(2) by blast
  next
    case (ExtnL A A' x B)
    from translate_Ext_inv [OF Meq [unfolded ExtnL(1), symmetric]]
    obtain M1 M2 where Mshape: "M = EnvEps_Syntax.Ext M1 x M2" and M1eq: "A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
    have lt: "size A < size a" unfolding ExtnL(1) by simp
    from less.hyps [OF lt ExtnL(3) M1eq] obtain N1 L1
      where N1eq: "\<lbrakk>N1\<rbrakk> = A'" and N1L1: "N1 \<rightarrow>E\<^sup>* L1" and M1L1: "M1 \<rightarrow>E\<^sup>* L1" by blast
    define N where "N = EnvEps_Syntax.Ext N1 x M2"
    define L where "L = EnvEps_Syntax.Ext L1 x M2"
    have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.Ext A' x B" unfolding N_def by (simp add: N1eq M2eq)
    moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N1L1 by (rule bs_steps_ExtnL)
    moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M1L1 by (rule bs_steps_ExtnL)
    ultimately show ?thesis unfolding ExtnL(2) by blast
  next
    case (ExtnR B B' A x)
    from translate_Ext_inv [OF Meq [unfolded ExtnR(1), symmetric]]
    obtain M1 M2 where Mshape: "M = EnvEps_Syntax.Ext M1 x M2" and M1eq: "A = \<lbrakk>M1\<rbrakk>" and M2eq: "B = \<lbrakk>M2\<rbrakk>" by blast
    have lt: "size B < size a" unfolding ExtnR(1) by simp
    from less.hyps [OF lt ExtnR(3) M2eq] obtain N2 L2
      where N2eq: "\<lbrakk>N2\<rbrakk> = B'" and N2L2: "N2 \<rightarrow>E\<^sup>* L2" and M2L2: "M2 \<rightarrow>E\<^sup>* L2" by blast
    define N where "N = EnvEps_Syntax.Ext M1 x N2"
    define L where "L = EnvEps_Syntax.Ext M1 x L2"
    have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.Ext A x B'" unfolding N_def by (simp add: N2eq M1eq)
    moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N2L2 by (rule bs_steps_ExtnR)
    moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M2L2 by (rule bs_steps_ExtnR)
    ultimately show ?thesis unfolding ExtnR(2) by blast
  next
    case (EnvAbst A A')
    from translate_Eps_inv [OF Meq [unfolded EnvAbst(1), symmetric]]
    obtain M1 where Mshape: "M = EnvEps_Syntax.Eps M1" and M1eq: "A = \<lbrakk>M1\<rbrakk>" by blast
    have lt: "size A < size a" unfolding EnvAbst(1) by simp
    from less.hyps [OF lt EnvAbst(3) M1eq] obtain N1 L1
      where N1eq: "\<lbrakk>N1\<rbrakk> = A'" and N1L1: "N1 \<rightarrow>E\<^sup>* L1" and M1L1: "M1 \<rightarrow>E\<^sup>* L1" by blast
    define N where "N = EnvEps_Syntax.Eps N1"
    define L where "L = EnvEps_Syntax.Eps L1"
    have "\<lbrakk>N\<rbrakk> = FREnv_Syntax.Eps A'" unfolding N_def by (simp add: N1eq)
    moreover have "N \<rightarrow>E\<^sup>* L" unfolding N_def L_def using N1L1 by (rule bs_steps_Eop)
    moreover have "M \<rightarrow>E\<^sup>* L" unfolding Mshape L_def using M1L1 by (rule bs_steps_Eop)
    ultimately show ?thesis unfolding EnvAbst(2) by blast
  qed
qed

theorem translate_single_step_lifting:
  assumes "FREnv_BetaSigma.beta_sigma_step \<lbrakk>M\<rbrakk> N'"
  shows "\<exists>N L. \<lbrakk>N\<rbrakk> = N'
           \<and> EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* N L
           \<and> EnvEps_BetaSigma.beta_sigma_step\<^sup>*\<^sup>* M L"
  using translate_single_step_lifting_aux [OF assms refl] .

end
