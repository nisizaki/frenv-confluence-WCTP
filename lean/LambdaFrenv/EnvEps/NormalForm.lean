import LambdaFrenv.EnvEps.SigmaConfluence

/-!
# Sigma-normal forms

Sigma reduction is terminating and confluent, so every term has a unique
sigma-normal form `snf M`.  This file introduces it, proves the algebraic
laws it satisfies, and characterizes the sigma-normal terms by a grammar
(`IsSNF`), mirroring `isabelle/EnvEps/EnvEps_Sigma_Normal_Form.thy` and
`EnvEps_Sigma_Normal_Form_Grammar.thy`.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-- A term is sigma-normal when no sigma step applies to it. -/
def SNormal (M : ETrm V C) : Prop := ∀ N, ¬ SStep M N

/-! ## Normality of the non-`comp` constructors -/

theorem snormal_var (x : V) : SNormal (ETrm.var x : ETrm V C) := by
  intro N h; cases h

theorem snormal_const (c : C) : SNormal (ETrm.const c : ETrm V C) := by
  intro N h; cases h

theorem snormal_id : SNormal (ETrm.id : ETrm V C) := by
  intro N h; cases h

theorem snormal_lam {A : ETrm V C} {x : V} : SNormal (ETrm.lam x A) ↔ SNormal A := by
  constructor
  · intro h A' hA'; exact h _ (SStep.lam hA')
  · intro h N hN; cases hN with | lam h' => exact h _ h'

theorem snormal_eps {A : ETrm V C} : SNormal (ETrm.eps A) ↔ SNormal A := by
  constructor
  · intro h A' hA'; exact h _ (SStep.eps hA')
  · intro h N hN; cases hN with | eps h' => exact h _ h'

theorem snormal_app {A B : ETrm V C} :
    SNormal (ETrm.app A B) ↔ (SNormal A ∧ SNormal B) := by
  constructor
  · intro h
    exact ⟨fun A' hA' => h _ (SStep.appL hA'), fun B' hB' => h _ (SStep.appR hB')⟩
  · rintro ⟨hA, hB⟩ N hN
    cases hN with
    | appL h' => exact hA _ h'
    | appR h' => exact hB _ h'

theorem snormal_ext {A B : ETrm V C} {x : V} :
    SNormal (ETrm.ext A x B) ↔ (SNormal A ∧ SNormal B) := by
  constructor
  · intro h
    exact ⟨fun A' hA' => h _ (SStep.extL hA'), fun B' hB' => h _ (SStep.extR hB')⟩
  · rintro ⟨hA, hB⟩ N hN
    cases hN with
    | extL h' => exact hA _ h'
    | extR h' => exact hB _ h'

/-! ## Existence and uniqueness of normal forms -/

theorem snf_exists (M : ETrm V C) : ∃ N, SSteps M N ∧ SNormal N := by
  have hacc := sstep_sn M
  induction hacc with
  | intro x _ ih =>
      by_cases h : ∃ y, SStep x y
      · obtain ⟨y, hy⟩ := h
        obtain ⟨N, h₁, h₂⟩ := ih y hy
        exact ⟨N, ReflTransGen.head hy h₁, h₂⟩
      · exact ⟨x, ReflTransGen.refl, fun N hN => h ⟨N, hN⟩⟩

theorem SNormal.eq_of_steps {M N : ETrm V C} (h : SNormal M) (hs : SSteps M N) : M = N := by
  rcases ReflTransGen.casesHead hs with rfl | ⟨c, hc, _⟩
  · rfl
  · exact absurd hc (h c)

theorem snf_unique {M N₁ N₂ : ETrm V C} (h₁ : SSteps M N₁) (n₁ : SNormal N₁)
    (h₂ : SSteps M N₂) (n₂ : SNormal N₂) : N₁ = N₂ := by
  obtain ⟨L, l₁, l₂⟩ := sstep_confluent h₁ h₂
  rw [n₁.eq_of_steps l₁, n₂.eq_of_steps l₂]

/-- The sigma-normal form of a term. -/
noncomputable def snf (M : ETrm V C) : ETrm V C := Classical.choose (snf_exists M)

theorem snf_steps (M : ETrm V C) : SSteps M (snf M) := (Classical.choose_spec (snf_exists M)).1

theorem snf_normal (M : ETrm V C) : SNormal (snf M) := (Classical.choose_spec (snf_exists M)).2

theorem snf_eq {M N : ETrm V C} (h : SSteps M N) (hn : SNormal N) : snf M = N :=
  snf_unique (snf_steps M) (snf_normal M) h hn

theorem snf_of_normal {M : ETrm V C} (hn : SNormal M) : snf M = M :=
  snf_eq ReflTransGen.refl hn

theorem snf_congr {M N : ETrm V C} (h : SSteps M N) : snf M = snf N :=
  snf_eq (ReflTransGen.trans h (snf_steps N)) (snf_normal N)

theorem snf_step {M N : ETrm V C} (h : SStep M N) : snf M = snf N :=
  snf_congr (ReflTransGen.single h)

theorem snf_idem (M : ETrm V C) : snf (snf M) = snf M := snf_of_normal (snf_normal M)

/-! ## The algebraic laws of `snf` -/

@[simp] theorem snf_var (x : V) : snf (ETrm.var x : ETrm V C) = ETrm.var x :=
  snf_of_normal (snormal_var x)

@[simp] theorem snf_const (c : C) : snf (ETrm.const c : ETrm V C) = ETrm.const c :=
  snf_of_normal (snormal_const c)

@[simp] theorem snf_id : snf (ETrm.id : ETrm V C) = ETrm.id :=
  snf_of_normal snormal_id

@[simp] theorem snf_lam (x : V) (A : ETrm V C) : snf (ETrm.lam x A) = ETrm.lam x (snf A) :=
  snf_eq (SSteps.lam (snf_steps A) x) (snormal_lam.2 (snf_normal A))

@[simp] theorem snf_eps (A : ETrm V C) : snf (ETrm.eps A) = ETrm.eps (snf A) :=
  snf_eq (SSteps.eps (snf_steps A)) (snormal_eps.2 (snf_normal A))

@[simp] theorem snf_app (A B : ETrm V C) : snf (ETrm.app A B) = ETrm.app (snf A) (snf B) :=
  snf_eq (SSteps.app (snf_steps A) (snf_steps B))
    (snormal_app.2 ⟨snf_normal A, snf_normal B⟩)

@[simp] theorem snf_ext (A : ETrm V C) (x : V) (B : ETrm V C) :
    snf (ETrm.ext A x B) = ETrm.ext (snf A) x (snf B) :=
  snf_eq (SSteps.ext (snf_steps A) x (snf_steps B))
    (snormal_ext.2 ⟨snf_normal A, snf_normal B⟩)

theorem snf_compL (A B : ETrm V C) : snf (ETrm.comp A B) = snf (ETrm.comp (snf A) B) :=
  snf_congr (SSteps.compL (snf_steps A) B)

theorem snf_compR (A B : ETrm V C) : snf (ETrm.comp A B) = snf (ETrm.comp A (snf B)) :=
  snf_congr (SSteps.compR A (snf_steps B))

theorem snf_comp (A B : ETrm V C) : snf (ETrm.comp A B) = snf (ETrm.comp (snf A) (snf B)) :=
  snf_congr (SSteps.comp (snf_steps A) (snf_steps B))

/-! ## The grammar of sigma-normal forms -/

/-- The grammar (2.32) of sigma-normal forms. -/
inductive IsSNF : ETrm V C → Prop where
  | var : IsSNF (ETrm.var x)
  | const : IsSNF (ETrm.const c)
  | id : IsSNF (ETrm.id : ETrm V C)
  | lam : IsSNF U → IsSNF (ETrm.lam x U)
  | app : IsSNF U → IsSNF W → IsSNF (ETrm.app U W)
  | ext : IsSNF U → IsSNF W → IsSNF (ETrm.ext U x W)
  | eps : IsSNF U → IsSNF (ETrm.eps U)
  | compLam : IsSNF U → IsSNF W → W ≠ ETrm.id →
      IsSNF (ETrm.comp (ETrm.lam x U) W)
  | compVar : IsSNF W → W ≠ ETrm.id → (∀ (P : ETrm V C) (y : V) (Q : ETrm V C), W ≠ ETrm.ext P y Q) →
      IsSNF (ETrm.comp (ETrm.var x) W)

/-- `comp (lam x U) W` is sigma-normal as soon as `U` and `W` are and `W ≠ id`. -/
theorem snormal_compLam {U W : ETrm V C} {x : V} (hU : SNormal U) (hW : SNormal W)
    (hne : W ≠ ETrm.id) : SNormal (ETrm.comp (ETrm.lam x U) W) := by
  intro N hN
  cases hN with
  | idR => exact hne rfl
  | compL h => cases h with | lam h' => exact hU _ h'
  | compR h => exact hW _ h

/-- `comp (var x) W` is sigma-normal as soon as `W` is, `W ≠ id`, and `W` is not
an environment extension. -/
theorem snormal_compVar {W : ETrm V C} {x : V} (hW : SNormal W) (hne : W ≠ ETrm.id)
    (hext : ∀ (P : ETrm V C) (y : V) (Q : ETrm V C), W ≠ ETrm.ext P y Q) :
    SNormal (ETrm.comp (ETrm.var x) W) := by
  intro N hN
  cases hN with
  | idR => exact hne rfl
  | varRef => exact hext _ _ _ rfl
  | varSkip _ => exact hext _ _ _ rfl
  | compL h => cases h
  | compR h => exact hW _ h

theorem IsSNF.snormal {M : ETrm V C} (h : IsSNF M) : SNormal M := by
  induction h with
  | var => exact snormal_var _
  | const => exact snormal_const _
  | id => exact snormal_id
  | lam _ ih => exact snormal_lam.2 ih
  | app _ _ ih₁ ih₂ => exact snormal_app.2 ⟨ih₁, ih₂⟩
  | ext _ _ ih₁ ih₂ => exact snormal_ext.2 ⟨ih₁, ih₂⟩
  | eps _ ih => exact snormal_eps.2 ih
  | compLam _ _ hne ih₁ ih₂ => exact snormal_compLam ih₁ ih₂ hne
  | compVar _ hne hext ih => exact snormal_compVar ih hne hext

theorem SNormal.isSNF {M : ETrm V C} (h : SNormal M) : IsSNF M := by
  induction M with
  | var x => exact IsSNF.var
  | const c => exact IsSNF.const
  | id => exact IsSNF.id
  | lam x A ih => exact IsSNF.lam (ih (snormal_lam.1 h))
  | eps A ih => exact IsSNF.eps (ih (snormal_eps.1 h))
  | app A B ih₁ ih₂ =>
      exact IsSNF.app (ih₁ (snormal_app.1 h).1) (ih₂ (snormal_app.1 h).2)
  | ext A x B ih₁ ih₂ =>
      exact IsSNF.ext (ih₁ (snormal_ext.1 h).1) (ih₂ (snormal_ext.1 h).2)
  | comp A B ih₁ ih₂ =>
      have hA : SNormal A := fun A' hA' => h _ (SStep.compL hA')
      have hB : SNormal B := fun B' hB' => h _ (SStep.compR hB')
      have hBid : B ≠ ETrm.id := by rintro rfl; exact h _ SStep.idR
      cases A with
      | var x =>
          refine IsSNF.compVar (ih₂ hB) hBid ?_
          rintro P y Q rfl
          by_cases hxy : y = x
          · subst hxy; exact h _ SStep.varRef
          · exact h _ (SStep.varSkip hxy)
      | const c => exact absurd (h _ SStep.constC) (fun hf => hf)
      | id => exact absurd (h _ SStep.idL) (fun hf => hf)
      | lam x U =>
          cases ih₁ hA with
          | lam hU => exact IsSNF.compLam hU (ih₂ hB) hBid
      | app P Q => exact absurd (h _ SStep.dApp) (fun hf => hf)
      | ext P y Q => exact absurd (h _ SStep.dExt) (fun hf => hf)
      | eps P => exact absurd (h _ SStep.epsEps) (fun hf => hf)
      | comp P Q => exact absurd (h _ SStep.assoc) (fun hf => hf)

theorem snormal_iff_isSNF {M : ETrm V C} : SNormal M ↔ IsSNF M :=
  ⟨SNormal.isSNF, IsSNF.snormal⟩

theorem isSNF_snf (M : ETrm V C) : IsSNF (snf M) := (snf_normal M).isSNF

end EnvEps

end LambdaFrenv
