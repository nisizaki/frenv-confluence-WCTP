import LambdaFrenv.EnvEps.Syntax

/-!
# The length measure and termination of sigma reduction

`elen` is the measure of `isabelle/EnvEps/EnvEps_Term_Length.thy`
(thesis Definition 11): it is multiplicative on `comp`, which is exactly
what makes `Assoc` and `DApp` decrease.  Every sigma rule strictly
decreases it, hence sigma reduction is strongly normalizing.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-! ## Arithmetic helpers

Lean's core `omega` handles linear goals only, so the products that occur
in the `comp` case are dealt with by hand.
-/

private theorem natMulPos {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h := Nat.mul_le_mul ha hb
  omega

private theorem natMulLtLeft {a b c : Nat} (ha : 0 < a) (h : b < c) : a * b < a * c := by
  have h1 : a * (b + 1) ≤ a * c := Nat.mul_le_mul (Nat.le_refl a) h
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

private theorem natMulLtRight {a b c : Nat} (hc : 0 < c) (h : a < b) : a * c < b * c := by
  have h1 : (a + 1) * c ≤ b * c := Nat.mul_le_mul h (Nat.le_refl c)
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

private theorem arithAssoc {a b c : Nat} (ha : 0 < a) (hc : 0 < c) :
    a * (b * (c + 1) + 1) < a * (b + 1) * (c + 1) := by
  rw [Nat.mul_assoc]
  refine natMulLtLeft ha ?_
  rw [Nat.add_mul, Nat.one_mul]
  omega

private theorem arithDistrib {l m n : Nat} (hn : 0 < n) :
    l * (n + 1) + m * (n + 1) + 1 < (l + m + 1) * (n + 1) := by
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

private theorem arithIdR {m : Nat} (hm : 0 < m) : m < m * (1 + 1) := by
  have h : m * 1 < m * (1 + 1) := natMulLtLeft hm (by omega)
  simpa using h

private theorem arithConst {n : Nat} (hn : 0 < n) : 1 < 1 * (n + 1) := by omega

private theorem arithEpsEps {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    2 * m < 2 * m * (n + 1) := by
  have h : 2 * m * 1 < 2 * m * (n + 1) := natMulLtLeft (by omega) (by omega)
  simpa using h

/-! ## The measure -/

/-- The length measure on `λ_EnvEps` terms. -/
def elen : ETrm V C → Nat
  | ETrm.var _ => 1
  | ETrm.const _ => 1
  | ETrm.id => 1
  | ETrm.lam _ M => 2 * elen M
  | ETrm.eps M => 2 * elen M
  | ETrm.app M N => elen M + elen N + 1
  | ETrm.ext M _ N => elen M + elen N + 1
  | ETrm.comp M N => elen M * (elen N + 1)

theorem elen_pos (M : ETrm V C) : 0 < elen M := by
  induction M with
  | var _ => simp [elen]
  | const _ => simp [elen]
  | id => simp [elen]
  | lam _ M ih => simp only [elen]; omega
  | eps M ih => simp only [elen]; omega
  | app M N ih₁ ih₂ => simp only [elen]; omega
  | ext M _ N ih₁ ih₂ => simp only [elen]; omega
  | comp M N ih₁ ih₂ => exact natMulPos ih₁ (by omega)

/-! ## Every sigma step decreases the measure -/

theorem SStep.elen_lt {M N : ETrm V C} (h : SStep M N) : elen N < elen M := by
  induction h with
  | assoc => simp only [elen]; exact arithAssoc (elen_pos _) (elen_pos _)
  | idL => simp only [elen]; omega
  | idR => simp only [elen]; exact arithIdR (elen_pos _)
  | dExt => simp only [elen]; exact arithDistrib (elen_pos _)
  | varRef => simp only [elen]; omega
  | varSkip _ => simp only [elen]; omega
  | dApp => simp only [elen]; exact arithDistrib (elen_pos _)
  | epsEps => simp only [elen]; exact arithEpsEps (elen_pos _) (elen_pos _)
  | constC => simp only [elen]; exact arithConst (elen_pos _)
  | appL _ ih => simp only [elen]; omega
  | appR _ ih => simp only [elen]; omega
  | lam _ ih => simp only [elen]; omega
  | extL _ ih => simp only [elen]; omega
  | extR _ ih => simp only [elen]; omega
  | compL _ ih => simp only [elen]; exact natMulLtRight (by omega) ih
  | compR _ ih => simp only [elen]; exact natMulLtLeft (elen_pos _) (by omega)
  | eps _ ih => simp only [elen]; omega

/-- Shrinking the left argument of a  shrinks the whole term. -/
theorem elen_comp_lt_left {X U : ETrm V C} (W : ETrm V C) (h : elen X < elen U) :
    elen (ETrm.comp X W) < elen (ETrm.comp U W) := by
  simp only [elen]
  exact natMulLtRight (by omega) h

/-- A -headed composition is strictly larger than its right argument. -/
theorem elen_lt_comp_lam {A L : ETrm V C} {x : V} :
    elen L < elen (ETrm.comp (ETrm.lam x A) L) := by
  have h1 : elen (ETrm.comp (ETrm.lam x A) L) = elen (ETrm.lam x A) * (elen L + 1) := by
    simp only [elen]
  have h2 : 2 <= elen (ETrm.lam x A) := by
    simp only [elen]; have := elen_pos A; omega
  have h3 : 2 * (elen L + 1) <= elen (ETrm.lam x A) * (elen L + 1) :=
    Nat.mul_le_mul h2 (Nat.le_refl _)
  omega

theorem elen_lt_app_left (X B : ETrm V C) : elen X < elen (ETrm.app X B) := by
  simp only [elen]; have := elen_pos B; omega

theorem elen_lt_app_right (X B : ETrm V C) : elen B < elen (ETrm.app X B) := by
  simp only [elen]; have := elen_pos X; omega

theorem elen_lt_ext_left (X : ETrm V C) (x : V) (B : ETrm V C) :
    elen X < elen (ETrm.ext X x B) := by
  simp only [elen]; have := elen_pos B; omega

theorem elen_lt_ext_right (X : ETrm V C) (x : V) (B : ETrm V C) :
    elen B < elen (ETrm.ext X x B) := by
  simp only [elen]; have := elen_pos X; omega

theorem elen_lt_comp_var {L : ETrm V C} {x : V} :
    elen L < elen (ETrm.comp (ETrm.var x) L) := by
  simp only [elen]; omega

/-- Sigma reduction is strongly normalizing. -/
theorem sstep_sn : SN (SStep (V := V) (C := C)) :=
  SN.ofMeasure elen (fun _ _ h => SStep.elen_lt h)

/-- A multi-step sigma reduction never increases the measure. -/
theorem SSteps.elen_le {M N : ETrm V C} (h : SSteps M N) : elen N ≤ elen M := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => exact Nat.le_trans (Nat.le_of_lt (SStep.elen_lt hstep)) ih

end EnvEps

end LambdaFrenv
