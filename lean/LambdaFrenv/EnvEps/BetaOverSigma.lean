import LambdaFrenv.EnvEps.Compat

/-!
# Beta over sigma, and confluence of `λ_EnvEps`

Sigma normalization does *not* commute with beta reduction step by step
(`→β*` and `→σ*` do not commute), but it does commute with parallel beta
reduction once the source has been fully sigma-normalized.  That is the
content of `key` below, the parallel-reduction form of Theorem 7 of the
Isabelle development
(`isabelle/EnvEps/EnvEps_Beta_Normal_Form_Simulation.thy`):

> `P ⇒β R` implies `snf P ⇒β S` for some `S` with `snf S = snf R`.

The relation `BOS M N` ("`N` is the sigma-normal form of a parallel beta
reduct of `M`") then inherits the diamond property from `PStep`, and
confluence of the full `→βσ` follows.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-! ## The key lemma -/

/-- Parallel beta reduction commutes with sigma normalization. -/
theorem key {P R : ETrm V C} (h : PStep P R) : ∃ S, PStep (snf P) S ∧ snf S = snf R := by
  induction h with
  | refl => exact ⟨snf _, PStep.refl, snf_idem _⟩
  | @lam A A' x _ ih =>
      obtain ⟨S₀, hS, eS⟩ := ih
      refine ⟨ETrm.lam x S₀, ?_, ?_⟩
      · rw [snf_lam]; exact PStep.lam hS
      · rw [snf_lam, snf_lam, eS]
  | @eps A A' _ ih =>
      obtain ⟨S₀, hS, eS⟩ := ih
      refine ⟨ETrm.eps S₀, ?_, ?_⟩
      · rw [snf_eps]; exact PStep.eps hS
      · rw [snf_eps, snf_eps, eS]
  | @app A A' B B' _ _ ihA ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      refine ⟨ETrm.app S₁ S₂, ?_, ?_⟩
      · rw [snf_app]; exact PStep.app hS₁ hS₂
      · rw [snf_app, snf_app, eS₁, eS₂]
  | @ext A A' B B' x _ _ ihA ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      refine ⟨ETrm.ext S₁ x S₂, ?_, ?_⟩
      · rw [snf_ext]; exact PStep.ext hS₁ hS₂
      · rw [snf_ext, snf_ext, eS₁, eS₂]
  | @comp A A' B B' _ _ ihA ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      obtain ⟨S, hS, eS⟩ := cc (snf_normal A) (snf_normal B) hS₁ hS₂
      refine ⟨S, ?_, ?_⟩
      · rw [snf_comp A B]; exact hS
      · rw [eS, snf_comp A' B', ← eS₁, ← eS₂, ← snf_comp S₁ S₂]
  | @beta A A' B B' x _ _ ihA ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      refine ⟨ETrm.comp S₁ (ETrm.ext S₂ x ETrm.id), ?_, ?_⟩
      · rw [snf_app, snf_lam]; exact PStep.beta hS₁ hS₂
      · exact snfCompExt eS₁ eS₂ rfl
  | @betaClos A A' L L' B B' x _ _ _ ihA ihL ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₃, hS₃, eS₃⟩ := ihL
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      have hsplit : snf (ETrm.app (ETrm.comp (ETrm.lam x A) L) B)
          = ETrm.app (snf (ETrm.comp (ETrm.lam x (snf A)) (snf L))) (snf B) := by
        rw [snf_app, snf_comp (ETrm.lam x A) L, snf_lam]
      by_cases hLid : snf L = ETrm.id
      · have hS₃id : S₃ = ETrm.id := PStep.id_inv (hLid ▸ hS₃)
        rw [hLid, snf_step (SStep.idR (M := ETrm.lam x (snf A))),
          snf_of_normal (snormal_lam.2 (snf_normal A))] at hsplit
        refine ⟨ETrm.comp S₁ (ETrm.ext S₂ x ETrm.id), ?_, ?_⟩
        · rw [hsplit]; exact PStep.beta hS₁ hS₂
        · refine snfCompExt eS₁ eS₂ ?_
          rw [← eS₃, hS₃id]
      · rw [snf_of_normal (snormal_compLam (snf_normal A) (snf_normal L) hLid)] at hsplit
        refine ⟨ETrm.comp S₁ (ETrm.ext S₂ x S₃), ?_, ?_⟩
        · rw [hsplit]; exact PStep.betaClos hS₁ hS₃ hS₂
        · exact snfCompExt eS₁ eS₂ eS₃
  | @compEps A A' B B' _ _ ihA ihB =>
      obtain ⟨S₁, hS₁, eS₁⟩ := ihA
      obtain ⟨S₂, hS₂, eS₂⟩ := ihB
      refine ⟨ETrm.comp S₁ S₂, ?_, ?_⟩
      · rw [snf_app, snf_eps]; exact PStep.compEps hS₁ hS₂
      · exact snfComp eS₁ eS₂

/-! ## Beta over sigma -/

/-- `BOS M N`: `N` is the sigma-normal form of a parallel beta reduct of `M`. -/
def BOS (M N : ETrm V C) : Prop := ∃ W, PStep M W ∧ N = snf W

theorem BOS.toBSSteps {M N : ETrm V C} (h : BOS M N) : BSSteps M N := by
  obtain ⟨W, hW, rfl⟩ := h
  exact ReflTransGen.trans (PStep.toBSSteps hW) (BSSteps.ofS (snf_steps W))

theorem bos_diamond : Diamond (BOS (V := V) (C := C)) := by
  intro M N₁ N₂ hb₁ hb₂
  obtain ⟨W₁, h₁, rfl⟩ := hb₁
  obtain ⟨W₂, h₂, rfl⟩ := hb₂
  obtain ⟨W₃, k₁, k₂⟩ := pstep_diamond h₁ h₂
  obtain ⟨X₁, hX₁, eX₁⟩ := key k₁
  obtain ⟨X₂, hX₂, eX₂⟩ := key k₂
  exact ⟨snf W₃, ⟨X₁, hX₁, eX₁.symm⟩, ⟨X₂, hX₂, eX₂.symm⟩⟩

theorem bos_of_bsstep {M N : ETrm V C} (h : BSStep M N) : BOS (snf M) (snf N) := by
  rcases h with hb | hs
  · obtain ⟨S, hS, eS⟩ := key (PStep.ofBStep hb)
    exact ⟨S, hS, eS.symm⟩
  · refine ⟨snf M, PStep.refl, ?_⟩
    rw [← snf_step hs, snf_idem]

theorem bos_steps_of_bssteps {M N : ETrm V C} (h : BSSteps M N) :
    ReflTransGen BOS (snf M) (snf N) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (bos_of_bsstep hstep)

/-! ## Confluence of `λ_EnvEps` -/

/-- Confluence of the full beta/sigma reduction of `λ_EnvEps`. -/
theorem bsstep_confluent : Confluent (BSStep (V := V) (C := C)) := by
  intro M N₁ N₂ h₁ h₂
  obtain ⟨L, l₁, l₂⟩ :=
    Diamond.confluent bos_diamond (bos_steps_of_bssteps h₁) (bos_steps_of_bssteps h₂)
  refine ⟨L, ?_, ?_⟩
  · exact ReflTransGen.trans (BSSteps.ofS (snf_steps N₁))
      (ReflTransGen.lift (fun _ _ hb => BOS.toBSSteps hb) l₁)
  · exact ReflTransGen.trans (BSSteps.ofS (snf_steps N₂))
      (ReflTransGen.lift (fun _ _ hb => BOS.toBSSteps hb) l₂)

end EnvEps

end LambdaFrenv
