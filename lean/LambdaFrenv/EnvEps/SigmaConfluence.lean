import LambdaFrenv.EnvEps.Length

/-!
# Local confluence and confluence of sigma reduction

This is the critical-pair analysis of `λ_EnvEps`'s sigma fragment
(`isabelle/EnvEps/EnvEps_Sigma_Root_Peaks.thy`,
`EnvEps_Sigma_Assoc_Peak.thy`, `EnvEps_Sigma_Inner_Peaks.thy`,
`EnvEps_Sigma_Local_Confluence.thy`).

All nine root rules have a `comp`-headed source, and they are pairwise
non-overlapping at the root, so each root rule needs to be checked only
against

* itself,
* `idR` (whose source `comp M id` unifies with several others),
* a congruence step below the root.

Together with strong normalization (`sstep_sn`) Newman's lemma then gives
confluence of `→σ`.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-- Joinability under sigma reduction. -/
def SJoin (M N : ETrm V C) : Prop := ∃ L, SSteps M L ∧ SSteps N L

namespace SJoin

theorem symm {M N : ETrm V C} : SJoin M N → SJoin N M
  | ⟨L, h₁, h₂⟩ => ⟨L, h₂, h₁⟩

theorem refl (M : ETrm V C) : SJoin M M := ⟨M, ReflTransGen.refl, ReflTransGen.refl⟩

theorem mk {M N L : ETrm V C} (h₁ : SSteps M L) (h₂ : SSteps N L) : SJoin M N := ⟨L, h₁, h₂⟩

/-- `M →σ* N` gives `SJoin M N`. -/
theorem left {M N : ETrm V C} (h : SSteps M N) : SJoin M N := ⟨N, h, ReflTransGen.refl⟩

/-- `N →σ* M` gives `SJoin M N`. -/
theorem right {M N : ETrm V C} (h : SSteps N M) : SJoin M N := ⟨M, ReflTransGen.refl, h⟩

end SJoin

private theorem s1 {M N : ETrm V C} (h : SStep M N) : SSteps M N :=
  ReflTransGen.single h

private theorem s2 {M N L : ETrm V C} (h₁ : SStep M N) (h₂ : SStep N L) : SSteps M L :=
  ReflTransGen.tail (s1 h₁) h₂

private theorem s3 {M N L P : ETrm V C} (h₁ : SStep M N) (h₂ : SStep N L) (h₃ : SStep L P) :
    SSteps M P :=
  ReflTransGen.tail (s2 h₁ h₂) h₃

/-! ## Root peaks

Each lemma takes an arbitrary sigma step out of the source of one root
rule and joins it with that rule's contractum.
-/

/-- Peaks over `comp (comp A B) D` (the associativity peak). -/
private theorem joinAssoc {A B D N₂ : ETrm V C}
    (h : SStep (ETrm.comp (ETrm.comp A B) D) N₂) :
    SJoin (ETrm.comp A (ETrm.comp B D)) N₂ := by
  cases h with
  | assoc => exact SJoin.refl _
  | idR => exact SJoin.left (s1 (SStep.compR SStep.idR))
  | compR h' => exact SJoin.mk (s1 (SStep.compR (SStep.compR h'))) (s1 SStep.assoc)
  | compL h' =>
      cases h' with
      | assoc =>
          exact SJoin.mk (s1 SStep.assoc) (s2 SStep.assoc (SStep.compR SStep.assoc))
      | idL => exact SJoin.left (s1 SStep.idL)
      | idR => exact SJoin.left (s1 (SStep.compR SStep.idL))
      | dExt =>
          exact SJoin.mk (s1 SStep.dExt)
            (s3 SStep.dExt (SStep.extL SStep.assoc) (SStep.extR SStep.assoc))
      | varRef => exact SJoin.left (s2 (SStep.compR SStep.dExt) SStep.varRef)
      | varSkip hxy =>
          exact SJoin.mk (s2 (SStep.compR SStep.dExt) (SStep.varSkip hxy)) (s1 SStep.assoc)
      | dApp =>
          exact SJoin.mk (s1 SStep.dApp)
            (s3 SStep.dApp (SStep.appL SStep.assoc) (SStep.appR SStep.assoc))
      | epsEps => exact SJoin.mk (s1 SStep.epsEps) (s1 SStep.epsEps)
      | constC => exact SJoin.mk (s1 SStep.constC) (s1 SStep.constC)
      | compL h'' => exact SJoin.mk (s1 (SStep.compL h'')) (s1 SStep.assoc)
      | compR h'' => exact SJoin.mk (s1 (SStep.compR (SStep.compL h''))) (s1 SStep.assoc)

/-- Peaks over `comp id B`. -/
private theorem joinIdL {B N₂ : ETrm V C} (h : SStep (ETrm.comp ETrm.id B) N₂) :
    SJoin B N₂ := by
  cases h with
  | idL => exact SJoin.refl _
  | idR => exact SJoin.refl _
  | compL h' => cases h'
  | compR h' => exact SJoin.mk (s1 h') (s1 SStep.idL)

/-- Peaks over `comp A id`. -/
private theorem joinIdR {A N₂ : ETrm V C} (h : SStep (ETrm.comp A ETrm.id) N₂) :
    SJoin A N₂ := by
  cases h with
  | assoc => exact SJoin.right (s1 (SStep.compR SStep.idR))
  | idL => exact SJoin.refl _
  | idR => exact SJoin.refl _
  | dExt => exact SJoin.right (s2 (SStep.extL SStep.idR) (SStep.extR SStep.idR))
  | dApp => exact SJoin.right (s2 (SStep.appL SStep.idR) (SStep.appR SStep.idR))
  | epsEps => exact SJoin.refl _
  | constC => exact SJoin.refl _
  | compL h' => exact SJoin.mk (s1 h') (s1 SStep.idR)
  | compR h' => cases h'

/-- Peaks over `comp (ext A x B) D`. -/
private theorem joinDExt {A B D N₂ : ETrm V C} {x : V}
    (h : SStep (ETrm.comp (ETrm.ext A x B) D) N₂) :
    SJoin (ETrm.ext (ETrm.comp A D) x (ETrm.comp B D)) N₂ := by
  cases h with
  | idR => exact SJoin.left (s2 (SStep.extL SStep.idR) (SStep.extR SStep.idR))
  | dExt => exact SJoin.refl _
  | compL h' =>
      cases h' with
      | extL h'' => exact SJoin.mk (s1 (SStep.extL (SStep.compL h''))) (s1 SStep.dExt)
      | extR h'' => exact SJoin.mk (s1 (SStep.extR (SStep.compL h''))) (s1 SStep.dExt)
  | compR h' =>
      exact SJoin.mk (s2 (SStep.extL (SStep.compR h')) (SStep.extR (SStep.compR h')))
        (s1 SStep.dExt)

/-- Peaks over `comp (var x) (ext A x B)`. -/
private theorem joinVarRef {A B N₂ : ETrm V C} {x : V}
    (h : SStep (ETrm.comp (ETrm.var x) (ETrm.ext A x B)) N₂) : SJoin A N₂ := by
  cases h with
  | varRef => exact SJoin.refl _
  | varSkip hxy => exact absurd rfl hxy
  | compL h' => cases h'
  | compR h' =>
      cases h' with
      | extL h'' => exact SJoin.mk (s1 h'') (s1 SStep.varRef)
      | extR h'' => exact SJoin.right (s1 SStep.varRef)

/-- Peaks over `comp (var y) (ext A x B)` with `x ≠ y`. -/
private theorem joinVarSkip {A B N₂ : ETrm V C} {x y : V} (hxy : x ≠ y)
    (h : SStep (ETrm.comp (ETrm.var y) (ETrm.ext A x B)) N₂) :
    SJoin (ETrm.comp (ETrm.var y) B) N₂ := by
  cases h with
  | varRef => exact absurd rfl hxy
  | varSkip _ => exact SJoin.refl _
  | compL h' => cases h'
  | compR h' =>
      cases h' with
      | extL h'' => exact SJoin.right (s1 (SStep.varSkip hxy))
      | extR h'' => exact SJoin.mk (s1 (SStep.compR h'')) (s1 (SStep.varSkip hxy))

/-- Peaks over `comp (app A B) D`. -/
private theorem joinDApp {A B D N₂ : ETrm V C}
    (h : SStep (ETrm.comp (ETrm.app A B) D) N₂) :
    SJoin (ETrm.app (ETrm.comp A D) (ETrm.comp B D)) N₂ := by
  cases h with
  | idR => exact SJoin.left (s2 (SStep.appL SStep.idR) (SStep.appR SStep.idR))
  | dApp => exact SJoin.refl _
  | compL h' =>
      cases h' with
      | appL h'' => exact SJoin.mk (s1 (SStep.appL (SStep.compL h''))) (s1 SStep.dApp)
      | appR h'' => exact SJoin.mk (s1 (SStep.appR (SStep.compL h''))) (s1 SStep.dApp)
  | compR h' =>
      exact SJoin.mk (s2 (SStep.appL (SStep.compR h')) (SStep.appR (SStep.compR h')))
        (s1 SStep.dApp)

/-- Peaks over `comp (eps A) D`. -/
private theorem joinEpsEps {A D N₂ : ETrm V C}
    (h : SStep (ETrm.comp (ETrm.eps A) D) N₂) : SJoin (ETrm.eps A) N₂ := by
  cases h with
  | idR => exact SJoin.refl _
  | epsEps => exact SJoin.refl _
  | compL h' =>
      cases h' with
      | eps h'' => exact SJoin.mk (s1 (SStep.eps h'')) (s1 SStep.epsEps)
  | compR h' => exact SJoin.right (s1 SStep.epsEps)

/-- Peaks over `comp (const c) D`. -/
private theorem joinConstC {D N₂ : ETrm V C} {c : C}
    (h : SStep (ETrm.comp (ETrm.const c) D) N₂) : SJoin (ETrm.const c) N₂ := by
  cases h with
  | idR => exact SJoin.refl _
  | constC => exact SJoin.refl _
  | compL h' => cases h'
  | compR h' => exact SJoin.right (s1 SStep.constC)

/-! ## Local confluence -/

theorem sstep_locally_confluent : LocallyConfluent (SStep (V := V) (C := C)) := by
  intro M N₁ N₂ h₁
  induction h₁ generalizing N₂ with
  | assoc => intro h₂; exact joinAssoc h₂
  | idL => intro h₂; exact joinIdL h₂
  | idR => intro h₂; exact joinIdR h₂
  | dExt => intro h₂; exact joinDExt h₂
  | varRef => intro h₂; exact joinVarRef h₂
  | varSkip hxy => intro h₂; exact joinVarSkip hxy h₂
  | dApp => intro h₂; exact joinDApp h₂
  | epsEps => intro h₂; exact joinEpsEps h₂
  | constC => intro h₂; exact joinConstC h₂
  | appL h ih =>
      intro h₂
      cases h₂ with
      | appL h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.appL k₁ _, SSteps.appL k₂ _⟩
      | appR h' => exact ⟨_, SSteps.appR _ (s1 h'), SSteps.appL (s1 h) _⟩
  | appR h ih =>
      intro h₂
      cases h₂ with
      | appL h' => exact ⟨_, SSteps.appL (s1 h') _, SSteps.appR _ (s1 h)⟩
      | appR h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.appR _ k₁, SSteps.appR _ k₂⟩
  | lam h ih =>
      intro h₂
      cases h₂ with
      | lam h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.lam k₁ _, SSteps.lam k₂ _⟩
  | extL h ih =>
      intro h₂
      cases h₂ with
      | extL h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.extL k₁ _ _, SSteps.extL k₂ _ _⟩
      | extR h' => exact ⟨_, SSteps.extR _ _ (s1 h'), SSteps.extL (s1 h) _ _⟩
  | extR h ih =>
      intro h₂
      cases h₂ with
      | extL h' => exact ⟨_, SSteps.extL (s1 h') _ _, SSteps.extR _ _ (s1 h)⟩
      | extR h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.extR _ _ k₁, SSteps.extR _ _ k₂⟩
  | eps h ih =>
      intro h₂
      cases h₂ with
      | eps h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.eps k₁, SSteps.eps k₂⟩
  | compL h ih =>
      intro h₂
      cases h₂ with
      | assoc => exact (joinAssoc (SStep.compL h)).symm
      | idL => cases h
      | idR => exact (joinIdR (SStep.compL h)).symm
      | dExt => exact (joinDExt (SStep.compL h)).symm
      | varRef => cases h
      | varSkip _ => cases h
      | dApp => exact (joinDApp (SStep.compL h)).symm
      | epsEps => exact (joinEpsEps (SStep.compL h)).symm
      | constC => cases h
      | compL h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.compL k₁ _, SSteps.compL k₂ _⟩
      | compR h' => exact ⟨_, SSteps.compR _ (s1 h'), SSteps.compL (s1 h) _⟩
  | compR h ih =>
      intro h₂
      cases h₂ with
      | assoc => exact (joinAssoc (SStep.compR h)).symm
      | idL => exact (joinIdL (SStep.compR h)).symm
      | idR => cases h
      | dExt => exact (joinDExt (SStep.compR h)).symm
      | varRef => exact (joinVarRef (SStep.compR h)).symm
      | varSkip hxy => exact (joinVarSkip hxy (SStep.compR h)).symm
      | dApp => exact (joinDApp (SStep.compR h)).symm
      | epsEps => exact (joinEpsEps (SStep.compR h)).symm
      | constC => exact (joinConstC (SStep.compR h)).symm
      | compL h' => exact ⟨_, SSteps.compL (s1 h') _, SSteps.compR _ (s1 h)⟩
      | compR h' =>
          obtain ⟨L, k₁, k₂⟩ := ih h'
          exact ⟨_, SSteps.compR _ k₁, SSteps.compR _ k₂⟩

/-! ## Confluence -/

/-- Sigma reduction is confluent (Newman's lemma applied to
`sstep_sn` and `sstep_locally_confluent`). -/
theorem sstep_confluent : Confluent (SStep (V := V) (C := C)) :=
  newman sstep_sn sstep_locally_confluent

end EnvEps

end LambdaFrenv
