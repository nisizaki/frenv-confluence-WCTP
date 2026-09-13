import LambdaFrenv.EnvEps.NormalForm

/-!
# Parallel beta reduction and its diamond property

The beta fragment of `λ_EnvEps` is *orthogonal*: its three root rules
`beta`, `betaClos` and `compEps` are left-linear, pairwise
non-overlapping (their sources are `app (lam ..) _`,
`app (comp (lam ..) _) _` and `app (eps ..) _`), and no proper subterm of
a source is itself a redex.  Consequently the Tait / Martin-Löf parallel
closure `PStep` has the diamond property, proved here by the complete
development `bcd` and the triangle property.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-- Parallel beta reduction. -/
inductive PStep : ETrm V C → ETrm V C → Prop where
  | refl : PStep M M
  | lam : PStep M M' → PStep (ETrm.lam x M) (ETrm.lam x M')
  | eps : PStep M M' → PStep (ETrm.eps M) (ETrm.eps M')
  | app : PStep M M' → PStep N N' → PStep (ETrm.app M N) (ETrm.app M' N')
  | ext : PStep M M' → PStep N N' → PStep (ETrm.ext M x N) (ETrm.ext M' x N')
  | comp : PStep M M' → PStep N N' → PStep (ETrm.comp M N) (ETrm.comp M' N')
  | beta : PStep M M' → PStep N N' →
      PStep (ETrm.app (ETrm.lam x M) N) (ETrm.comp M' (ETrm.ext N' x ETrm.id))
  | betaClos : PStep M M' → PStep L L' → PStep N N' →
      PStep (ETrm.app (ETrm.comp (ETrm.lam x M) L) N) (ETrm.comp M' (ETrm.ext N' x L'))
  | compEps : PStep M M' → PStep N N' →
      PStep (ETrm.app (ETrm.eps M) N) (ETrm.comp M' N')

/-! ## Inversion -/

theorem PStep.var_inv {x : V} {Q : ETrm V C} (h : PStep (ETrm.var x) Q) : Q = ETrm.var x := by
  cases h with | refl => rfl

theorem PStep.const_inv {c : C} {Q : ETrm V C} (h : PStep (ETrm.const c) Q) :
    Q = ETrm.const c := by
  cases h with | refl => rfl

theorem PStep.id_inv {Q : ETrm V C} (h : PStep (ETrm.id : ETrm V C) Q) : Q = ETrm.id := by
  cases h with | refl => rfl

theorem PStep.lam_inv {x : V} {A Q : ETrm V C} (h : PStep (ETrm.lam x A) Q) :
    ∃ A', Q = ETrm.lam x A' ∧ PStep A A' := by
  cases h with
  | refl => exact ⟨A, rfl, PStep.refl⟩
  | lam h' => exact ⟨_, rfl, h'⟩

theorem PStep.eps_inv {A Q : ETrm V C} (h : PStep (ETrm.eps A) Q) :
    ∃ A', Q = ETrm.eps A' ∧ PStep A A' := by
  cases h with
  | refl => exact ⟨A, rfl, PStep.refl⟩
  | eps h' => exact ⟨_, rfl, h'⟩

theorem PStep.ext_inv {x : V} {A B Q : ETrm V C} (h : PStep (ETrm.ext A x B) Q) :
    ∃ A' B', Q = ETrm.ext A' x B' ∧ PStep A A' ∧ PStep B B' := by
  cases h with
  | refl => exact ⟨A, B, rfl, PStep.refl, PStep.refl⟩
  | ext h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem PStep.comp_inv {A B Q : ETrm V C} (h : PStep (ETrm.comp A B) Q) :
    ∃ A' B', Q = ETrm.comp A' B' ∧ PStep A A' ∧ PStep B B' := by
  cases h with
  | refl => exact ⟨A, B, rfl, PStep.refl, PStep.refl⟩
  | comp h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem PStep.of_lam {x : V} {A A' : ETrm V C} (h : PStep (ETrm.lam x A) (ETrm.lam x A')) :
    PStep A A' := by
  cases h with
  | refl => exact PStep.refl
  | lam h' => exact h'

theorem PStep.of_eps {A A' : ETrm V C} (h : PStep (ETrm.eps A) (ETrm.eps A')) : PStep A A' := by
  cases h with
  | refl => exact PStep.refl
  | eps h' => exact h'

theorem PStep.of_comp {A A' B B' : ETrm V C}
    (h : PStep (ETrm.comp A B) (ETrm.comp A' B')) : PStep A A' ∧ PStep B B' := by
  cases h with
  | refl => exact ⟨PStep.refl, PStep.refl⟩
  | comp h₁ h₂ => exact ⟨h₁, h₂⟩

/-! ## Relation to one-step beta reduction -/

theorem PStep.ofBStep {M N : ETrm V C} (h : BStep M N) : PStep M N := by
  induction h with
  | beta => exact PStep.beta PStep.refl PStep.refl
  | betaClos => exact PStep.betaClos PStep.refl PStep.refl PStep.refl
  | compEps => exact PStep.compEps PStep.refl PStep.refl
  | appL _ ih => exact PStep.app ih PStep.refl
  | appR _ ih => exact PStep.app PStep.refl ih
  | lam _ ih => exact PStep.lam ih
  | extL _ ih => exact PStep.ext ih PStep.refl
  | extR _ ih => exact PStep.ext PStep.refl ih
  | compL _ ih => exact PStep.comp ih PStep.refl
  | compR _ ih => exact PStep.comp PStep.refl ih
  | eps _ ih => exact PStep.eps ih

theorem PStep.toBSteps {M N : ETrm V C} (h : PStep M N) : BSteps M N := by
  induction h with
  | refl => exact ReflTransGen.refl
  | lam _ ih => exact BSteps.lam ih _
  | eps _ ih => exact BSteps.eps ih
  | app _ _ ih₁ ih₂ => exact BSteps.app ih₁ ih₂
  | ext _ _ ih₁ ih₂ => exact BSteps.ext ih₁ _ ih₂
  | comp _ _ ih₁ ih₂ => exact BSteps.comp ih₁ ih₂
  | beta _ _ ih₁ ih₂ =>
      exact ReflTransGen.tail (BSteps.app (BSteps.lam ih₁ _) ih₂) BStep.beta
  | betaClos _ _ _ ih₁ ih₂ ih₃ =>
      exact ReflTransGen.tail
        (BSteps.app (BSteps.comp (BSteps.lam ih₁ _) ih₂) ih₃) BStep.betaClos
  | compEps _ _ ih₁ ih₂ =>
      exact ReflTransGen.tail (BSteps.app (BSteps.eps ih₁) ih₂) BStep.compEps

theorem PStep.toBSSteps {M N : ETrm V C} (h : PStep M N) : BSSteps M N :=
  BSSteps.ofB h.toBSteps

/-! ## The complete development -/

/-- The complete beta development: every beta redex present in the term is
contracted simultaneously. -/
def bcd : ETrm V C → ETrm V C
  | ETrm.var x => ETrm.var x
  | ETrm.const c => ETrm.const c
  | ETrm.id => ETrm.id
  | ETrm.lam x M => ETrm.lam x (bcd M)
  | ETrm.eps M => ETrm.eps (bcd M)
  | ETrm.ext M x N => ETrm.ext (bcd M) x (bcd N)
  | ETrm.comp M N => ETrm.comp (bcd M) (bcd N)
  | ETrm.app (ETrm.lam x M) N => ETrm.comp (bcd M) (ETrm.ext (bcd N) x ETrm.id)
  | ETrm.app (ETrm.eps M) N => ETrm.comp (bcd M) (bcd N)
  | ETrm.app (ETrm.comp (ETrm.lam x M) L) N =>
      ETrm.comp (bcd M) (ETrm.ext (bcd N) x (bcd L))
  | ETrm.app A N => ETrm.app (bcd A) (bcd N)

theorem pstep_bcd (M : ETrm V C) : PStep M (bcd M) := by
  induction M with
  | var x => exact PStep.refl
  | const c => exact PStep.refl
  | id => exact PStep.refl
  | lam x A ih => exact PStep.lam ih
  | eps A ih => exact PStep.eps ih
  | ext A x B ih₁ ih₂ => exact PStep.ext ih₁ ih₂
  | comp A B ih₁ ih₂ => exact PStep.comp ih₁ ih₂
  | app A B ihA ihB =>
      cases A with
      | var y => exact PStep.app ihA ihB
      | const c => exact PStep.app ihA ihB
      | id => exact PStep.app ihA ihB
      | app P Q => exact PStep.app ihA ihB
      | ext P y Q => exact PStep.app ihA ihB
      | lam x P =>
          exact PStep.beta (PStep.of_lam ihA) ihB
      | eps P =>
          exact PStep.compEps (PStep.of_eps ihA) ihB
      | comp A₁ L =>
          cases A₁ with
          | lam x P =>
              obtain ⟨h₁, h₂⟩ := PStep.of_comp ihA
              exact PStep.betaClos (PStep.of_lam h₁) h₂ ihB
          | var y => exact PStep.app ihA ihB
          | const c => exact PStep.app ihA ihB
          | id => exact PStep.app ihA ihB
          | app P Q => exact PStep.app ihA ihB
          | ext P y Q => exact PStep.app ihA ihB
          | eps P => exact PStep.app ihA ihB
          | comp P Q => exact PStep.app ihA ihB

/-- The triangle property: every parallel reduct of `M` reduces in one
further parallel step to the complete development of `M`. -/
theorem PStep.triangle {M N : ETrm V C} (h : PStep M N) : PStep N (bcd M) := by
  induction h with
  | refl => exact pstep_bcd _
  | lam _ ih => exact PStep.lam ih
  | eps _ ih => exact PStep.eps ih
  | ext _ _ ih₁ ih₂ => exact PStep.ext ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact PStep.comp ih₁ ih₂
  | beta _ _ ih₁ ih₂ => exact PStep.comp ih₁ (PStep.ext ih₂ PStep.refl)
  | betaClos _ _ _ ih₁ ih₂ ih₃ => exact PStep.comp ih₁ (PStep.ext ih₃ ih₂)
  | compEps _ _ ih₁ ih₂ => exact PStep.comp ih₁ ih₂
  | @app A A' B B' hA hB ihA ihB =>
      cases A with
      | var y => exact PStep.app ihA ihB
      | const c => exact PStep.app ihA ihB
      | id => exact PStep.app ihA ihB
      | app P Q => exact PStep.app ihA ihB
      | ext P y Q => exact PStep.app ihA ihB
      | lam x P =>
          obtain ⟨P', rfl, _⟩ := PStep.lam_inv hA
          exact PStep.beta (PStep.of_lam ihA) ihB
      | eps P =>
          obtain ⟨P', rfl, _⟩ := PStep.eps_inv hA
          exact PStep.compEps (PStep.of_eps ihA) ihB
      | comp A₁ L =>
          cases A₁ with
          | lam x P =>
              obtain ⟨A₁', L', rfl, hA₁, _⟩ := PStep.comp_inv hA
              obtain ⟨P', rfl, _⟩ := PStep.lam_inv hA₁
              obtain ⟨k₁, k₂⟩ := PStep.of_comp ihA
              exact PStep.betaClos (PStep.of_lam k₁) k₂ ihB
          | var y => exact PStep.app ihA ihB
          | const c => exact PStep.app ihA ihB
          | id => exact PStep.app ihA ihB
          | app P Q => exact PStep.app ihA ihB
          | ext P y Q => exact PStep.app ihA ihB
          | eps P => exact PStep.app ihA ihB
          | comp P Q => exact PStep.app ihA ihB

/-- Parallel beta reduction has the diamond property. -/
theorem pstep_diamond : Diamond (PStep (V := V) (C := C)) := by
  intro M N₁ N₂ h₁ h₂
  exact ⟨bcd M, h₁.triangle, h₂.triangle⟩

end EnvEps

end LambdaFrenv
