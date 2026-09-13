import LambdaFrenv.Translation
import LambdaFrenv.ParNotStrong

/-!
# Main results

`frenv_beta_sigma_confluent` is the Lean counterpart of the Isabelle
declaration
`FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent`:
any two finite beta/sigma reduction sequences out of the same `λ_FREnv`
term have a common reduct.
-/

namespace LambdaFrenv

universe u v

variable {V : Type u} {C : Type v}

/-- **Full confluence of `λ_FREnv`.**  If `P →βσ* Q₁` and `P →βσ* Q₂`, then
`Q₁` and `Q₂` have a common `→βσ*` reduct. -/
theorem frenv_beta_sigma_confluent {P Q₁ Q₂ : Trm V C}
    (h₁ : BetaSigmaSteps P Q₁) (h₂ : BetaSigmaSteps P Q₂) :
    ∃ L, BetaSigmaSteps Q₁ L ∧ BetaSigmaSteps Q₂ L :=
  frenv_confluent h₁ h₂

/-- The same statement phrased with `Joinable`. -/
theorem frenv_beta_sigma_joinable {P Q₁ Q₂ : Trm V C}
    (h₁ : BetaSigmaSteps P Q₁) (h₂ : BetaSigmaSteps P Q₂) :
    Joinable BetaSigmaStep Q₁ Q₂ :=
  frenv_confluent h₁ h₂

/-- Local confluence, an immediate corollary of full confluence. -/
theorem frenv_locally_confluent : LocallyConfluent (BetaSigmaStep (V := V) (C := C)) :=
  fun _ _ _ h₁ h₂ =>
    frenv_confluent (ReflTransGen.single h₁) (ReflTransGen.single h₂)

end LambdaFrenv
