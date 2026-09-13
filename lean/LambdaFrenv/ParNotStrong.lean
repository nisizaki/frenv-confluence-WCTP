import LambdaFrenv.Par

/-!
# `ParStronglyConfluent` is refutable

`LambdaFrenv/Par.lean` states `ParStronglyConfluent` — the diamond
property of `ParStep` — as the next milestone.  It is in fact **false**
whenever there is at least one variable, and this file proves it.

The obstruction is the associativity rule `Assoc`, which turns
`(A∘B)∘C` into `A∘(B∘C)` where `A∘B` abbreviates `App (Eps A) B`.  On the
associativity pentagon

```text
T = ((v∘v)∘v)∘v
```

the root `Assoc` step and the `Assoc` step one level down produce

```text
N₁ = (v∘v)∘(v∘v)          N₂ = (v∘(v∘v))∘v
```

and each of `N₁`, `N₂` has exactly three parallel reducts (itself, its
root `Assoc` reduct and its root `DApp` reduct).  The two three-element
sets are disjoint, so no common single parallel step exists.  Associativity
is confluent but never *strongly* confluent; that is why the confluence
proof in this development goes through sigma-normalization instead.
-/

namespace LambdaFrenv

universe u v

variable {V : Type u} {C : Type v}

/-! ## Terms with no parallel redex -/

private theorem irredVar {x : V} {t : Trm V C} (h : ParStep (Trm.var x) t) :
    t = Trm.var x := by
  cases h with | refl => rfl

private theorem irredEpsVar {x : V} {t : Trm V C} (h : ParStep (Trm.eps (Trm.var x)) t) :
    t = Trm.eps (Trm.var x) := by
  cases h with
  | refl => rfl
  | eps h' => rw [irredVar h']

/-- `v∘v` is a parallel normal form. -/
private theorem irredVV {x : V} {t : Trm V C}
    (h : ParStep (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)) t) :
    t = Trm.app (Trm.eps (Trm.var x)) (Trm.var x) := by
  cases h with
  | refl => rfl
  | app h₁ h₂ => rw [irredEpsVar h₁, irredVar h₂]

private theorem irredEpsVV {x : V} {t : Trm V C}
    (h : ParStep (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) t) :
    t = Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)) := by
  cases h with
  | refl => rfl
  | eps h' => rw [irredVV h']

/-- `v∘(v∘v)` is a parallel normal form. -/
private theorem irredVVV {x : V} {t : Trm V C}
    (h : ParStep (Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) t) :
    t = Trm.app (Trm.eps (Trm.var x)) (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)) := by
  cases h with
  | refl => rfl
  | app h₁ h₂ => rw [irredEpsVar h₁, irredVV h₂]

private theorem irredEpsVVV {x : V} {t : Trm V C}
    (h : ParStep (Trm.eps (Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))) t) :
    t = Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) := by
  cases h with
  | refl => rfl
  | eps h' => rw [irredVVV h']

/-! ## The two peaks and all of their reducts -/

/-- Every parallel reduct of `N₁ = (v∘v)∘(v∘v)`. -/
private theorem reductsN1 {x : V} {t : Trm V C}
    (h : ParStep (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) t) :
    t = Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)) ∨
    t = Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) ∨
    t = Trm.app
          (Trm.app (Trm.eps (Trm.eps (Trm.var x)))
            (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) := by
  cases h with
  | refl => exact Or.inl rfl
  | app h₁ h₂ => exact Or.inl (by rw [irredEpsVV h₁, irredVV h₂])
  | assoc hL hM hN =>
      exact Or.inr (Or.inl (by rw [irredVar hL, irredVar hM, irredVV hN]))
  | dApp hM hN hL =>
      exact Or.inr (Or.inr (by rw [irredEpsVar hM, irredVar hN, irredVV hL]))

/-- Every parallel reduct of `N₂ = (v∘(v∘v))∘v`. -/
private theorem reductsN2 {x : V} {t : Trm V C}
    (h : ParStep (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x))
            (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))) (Trm.var x)) t) :
    t = Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))) (Trm.var x) ∨
    t = Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) (Trm.var x)) ∨
    t = Trm.app
          (Trm.app (Trm.eps (Trm.eps (Trm.var x))) (Trm.var x))
          (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) (Trm.var x)) := by
  cases h with
  | refl => exact Or.inl rfl
  | app h₁ h₂ => exact Or.inl (by rw [irredEpsVVV h₁, irredVar h₂])
  | assoc hL hM hN =>
      exact Or.inr (Or.inl (by rw [irredVar hL, irredVV hM, irredVar hN]))
  | dApp hM hN hL =>
      exact Or.inr (Or.inr (by rw [irredEpsVar hM, irredVV hN, irredVar hL]))

/-! ## The refutation -/

/-- Parallel reduction of `λ_FREnv` does **not** have the diamond property
as soon as there is a variable. -/
theorem not_parStronglyConfluent (x : V) : ¬ ParStronglyConfluent (V := V) (C := C) := by
  intro hsc
  have step₁ :
      ParStep
        (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.var x))) (Trm.var x) : Trm V C)
        (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x))) :=
    ParStep.assoc ParStep.refl ParStep.refl ParStep.refl
  have step₂ :
      ParStep
        (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))
          (Trm.var x))) (Trm.var x) : Trm V C)
        (Trm.app (Trm.eps (Trm.app (Trm.eps (Trm.var x))
          (Trm.app (Trm.eps (Trm.var x)) (Trm.var x)))) (Trm.var x)) :=
    ParStep.app (ParStep.eps (ParStep.assoc ParStep.refl ParStep.refl ParStep.refl))
      ParStep.refl
  obtain ⟨N, hN₁, hN₂⟩ := hsc step₁ step₂
  rcases reductsN1 hN₁ with rfl | rfl | rfl <;>
    rcases reductsN2 hN₂ with h | h | h <;> simp at h

end LambdaFrenv
