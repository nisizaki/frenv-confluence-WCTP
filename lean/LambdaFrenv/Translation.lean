import LambdaFrenv.Par
import LambdaFrenv.EnvEps.BetaOverSigma

/-!
# Translation from `λ_EnvEps` to `λ_FREnv`, and confluence of `λ_FREnv`

`tr` erases the primitive composition of `λ_EnvEps` by sending
`comp M N` to `App (Eps ⟦M⟧) ⟦N⟧`.  It is surjective (`tr_incl`) and it
simulates every `λ_EnvEps` step by zero or one `λ_FREnv` steps.

The interesting direction is the *lifting* lemma `lift1`: a single
`λ_FREnv` step out of `tr M` need not be the image of a step out of `M`,
because `tr` collapses `comp A B` and `app (eps A) B`.  What is true, and
enough, is that the step has a preimage `N` which shares a `λ_EnvEps`
reduct with `M`.  Combined with confluence of `λ_EnvEps` this transfers
confluence to `λ_FREnv`.
-/

namespace LambdaFrenv

open EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-! ## The translation -/

/-- `⟦-⟧ : λ_EnvEps → λ_FREnv`. -/
def tr : ETrm V C → Trm V C
  | ETrm.var x => Trm.var x
  | ETrm.const c => Trm.const c
  | ETrm.id => Trm.id
  | ETrm.lam x M => Trm.lam x (tr M)
  | ETrm.app M N => Trm.app (tr M) (tr N)
  | ETrm.ext M x N => Trm.ext (tr M) x (tr N)
  | ETrm.eps M => Trm.eps (tr M)
  | ETrm.comp M N => Trm.app (Trm.eps (tr M)) (tr N)

/-- The inclusion of `λ_FREnv` into `λ_EnvEps`. -/
def incl : Trm V C → ETrm V C
  | Trm.var x => ETrm.var x
  | Trm.const c => ETrm.const c
  | Trm.id => ETrm.id
  | Trm.lam x M => ETrm.lam x (incl M)
  | Trm.app M N => ETrm.app (incl M) (incl N)
  | Trm.ext M x N => ETrm.ext (incl M) x (incl N)
  | Trm.eps M => ETrm.eps (incl M)

/-- `tr` is surjective. -/
theorem tr_incl (T : Trm V C) : tr (incl T) = T := by
  induction T with
  | var x => rfl
  | const c => rfl
  | id => rfl
  | lam x A ih => simp [tr, incl, ih]
  | app A B ih₁ ih₂ => simp [tr, incl, ih₁, ih₂]
  | ext A x B ih₁ ih₂ => simp [tr, incl, ih₁, ih₂]
  | eps A ih => simp [tr, incl, ih]

/-! ## Inverting the translation -/

theorem tr_eq_var {M : ETrm V C} {x : V} (h : tr M = Trm.var x) : M = ETrm.var x := by
  cases M <;> simp_all [tr]

theorem tr_eq_const {M : ETrm V C} {c : C} (h : tr M = Trm.const c) : M = ETrm.const c := by
  cases M <;> simp_all [tr]

theorem tr_eq_id {M : ETrm V C} (h : tr M = Trm.id) : M = ETrm.id := by
  cases M <;> simp_all [tr]

theorem tr_eq_lam {M : ETrm V C} {x : V} {a : Trm V C} (h : tr M = Trm.lam x a) :
    ∃ A, M = ETrm.lam x A ∧ tr A = a := by
  cases M <;> simp_all [tr]

theorem tr_eq_eps {M : ETrm V C} {a : Trm V C} (h : tr M = Trm.eps a) :
    ∃ A, M = ETrm.eps A ∧ tr A = a := by
  cases M <;> simp_all [tr]

theorem tr_eq_ext {M : ETrm V C} {x : V} {a b : Trm V C} (h : tr M = Trm.ext a x b) :
    ∃ A B, M = ETrm.ext A x B ∧ tr A = a ∧ tr B = b := by
  cases M with
  | ext A y B =>
      simp [tr] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h2
      exact ⟨A, B, rfl, h1, h3⟩
  | var _ => simp [tr] at h
  | const _ => simp [tr] at h
  | id => simp [tr] at h
  | lam _ _ => simp [tr] at h
  | app _ _ => simp [tr] at h
  | eps _ => simp [tr] at h
  | comp _ _ => simp [tr] at h

theorem tr_eq_app {M : ETrm V C} {a b : Trm V C} (h : tr M = Trm.app a b) :
    (∃ A B, M = ETrm.app A B ∧ tr A = a ∧ tr B = b) ∨
    (∃ A B, M = ETrm.comp A B ∧ Trm.eps (tr A) = a ∧ tr B = b) := by
  cases M with
  | app A B => exact Or.inl ⟨A, B, rfl, by simp [tr] at h; exact h.1, by simp [tr] at h; exact h.2⟩
  | comp A B => exact Or.inr ⟨A, B, rfl, by simp [tr] at h; exact h.1, by simp [tr] at h; exact h.2⟩
  | var _ => simp [tr] at h
  | const _ => simp [tr] at h
  | id => simp [tr] at h
  | lam _ _ => simp [tr] at h
  | ext _ _ _ => simp [tr] at h
  | eps _ => simp [tr] at h

/-! ## Inversion lemmas on the two calculi -/

/-- The only `λ_FREnv` rule applicable to an `Eps`-headed term is `envAbst`. -/
theorem BetaSigmaStep.eps_inv {P Q : Trm V C} (h : BetaSigmaStep (Trm.eps P) Q) :
    ∃ Q', Q = Trm.eps Q' ∧ BetaSigmaStep P Q' := by
  cases h with | envAbst h' => exact ⟨_, rfl, h'⟩

theorem BSStep.eps_inv {A Q : ETrm V C} (h : BSStep (ETrm.eps A) Q) :
    ∃ A', Q = ETrm.eps A' ∧ BSStep A A' := by
  rcases h with hb | hs
  · cases hb with | eps h' => exact ⟨_, rfl, Or.inl h'⟩
  · cases hs with | eps h' => exact ⟨_, rfl, Or.inr h'⟩

theorem bsteps_eps_inv {P L : ETrm V C} (h : BSSteps P L) :
    ∀ A, P = ETrm.eps A → ∃ A₁, L = ETrm.eps A₁ ∧ BSSteps A A₁ := by
  induction h with
  | refl => intro A hA; exact ⟨A, hA, ReflTransGen.refl⟩
  | tail _ hstep ih =>
      intro A hA
      obtain ⟨A₁, rfl, hA₁⟩ := ih A hA
      obtain ⟨A₂, rfl, hA₂⟩ := BSStep.eps_inv hstep
      exact ⟨A₂, rfl, ReflTransGen.tail hA₁ hA₂⟩

/-! ## Simulation -/

private theorem eb {M N : ETrm V C} (h : BStep M N) : BSSteps M N := ReflTransGen.single (Or.inl h)

private theorem es {M N : ETrm V C} (h : SStep M N) : BSSteps M N := ReflTransGen.single (Or.inr h)

theorem tr_bstep {M N : ETrm V C} (h : BStep M N) : BetaSigmaSteps (tr M) (tr N) := by
  induction h with
  | beta => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.beta
  | betaClos => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.betaClos
  | compEps => simp only [tr]; exact ReflTransGen.refl
  | appL _ ih => exact BetaSigmaSteps.appL ih
  | appR _ ih => exact BetaSigmaSteps.appR ih
  | lam _ ih => exact BetaSigmaSteps.lam ih _
  | extL _ ih => exact BetaSigmaSteps.extL ih _
  | extR _ ih => exact BetaSigmaSteps.extR ih _
  | compL _ ih => exact BetaSigmaSteps.appL (BetaSigmaSteps.eps ih)
  | compR _ ih => exact BetaSigmaSteps.appR ih
  | eps _ ih => exact BetaSigmaSteps.eps ih

theorem tr_sstep {M N : ETrm V C} (h : SStep M N) : BetaSigmaSteps (tr M) (tr N) := by
  induction h with
  | assoc => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.assoc
  | idL => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.idL
  | idR => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.idR
  | dExt => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.dExt
  | varRef => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.varRef
  | varSkip hxy => simp only [tr]; exact ReflTransGen.single (BetaSigmaStep.varSkip hxy)
  | dApp => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.dApp
  | epsEps => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.stab
  | constC => simp only [tr]; exact ReflTransGen.single BetaSigmaStep.const
  | appL _ ih => exact BetaSigmaSteps.appL ih
  | appR _ ih => exact BetaSigmaSteps.appR ih
  | lam _ ih => exact BetaSigmaSteps.lam ih _
  | extL _ ih => exact BetaSigmaSteps.extL ih _
  | extR _ ih => exact BetaSigmaSteps.extR ih _
  | compL _ ih => exact BetaSigmaSteps.appL (BetaSigmaSteps.eps ih)
  | compR _ ih => exact BetaSigmaSteps.appR ih
  | eps _ ih => exact BetaSigmaSteps.eps ih

theorem tr_bsstep {M N : ETrm V C} (h : BSStep M N) : BetaSigmaSteps (tr M) (tr N) :=
  h.elim tr_bstep tr_sstep

theorem tr_bssteps {M N : ETrm V C} (h : BSSteps M N) : BetaSigmaSteps (tr M) (tr N) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.trans ih (tr_bsstep hstep)

/-! ## Lifting -/

/-- Every preimage of an `App (Eps _) _` reduces to a composition. -/
theorem app_eps_preimage {M : ETrm V C} {X Y : Trm V C} (h : tr M = Trm.app (Trm.eps X) Y) :
    ∃ A B, BSSteps M (ETrm.comp A B) ∧ tr A = X ∧ tr B = Y := by
  rcases tr_eq_app h with ⟨A, B, rfl, hA, hB⟩ | ⟨A, B, rfl, hA, hB⟩
  · obtain ⟨A₀, rfl, hA₀⟩ := tr_eq_eps hA
    exact ⟨A₀, B, eb BStep.compEps, hA₀, hB⟩
  · refine ⟨A, B, ReflTransGen.refl, ?_, hB⟩
    injection hA

/-- **Single-step lifting.** -/
theorem lift1 {P Q : Trm V C} (h : BetaSigmaStep P Q) :
    ∀ M : ETrm V C, tr M = P → ∃ N L, tr N = Q ∧ BSSteps N L ∧ BSSteps M L := by
  induction h with
  | @beta x m nn =>
      intro M hM
      rcases tr_eq_app hM with ⟨A, B, rfl, hA, hB⟩ | ⟨A, B, rfl, hA, hB⟩
      · obtain ⟨A₀, rfl, hA₀⟩ := tr_eq_lam hA
        exact ⟨ETrm.comp A₀ (ETrm.ext B x ETrm.id), ETrm.comp A₀ (ETrm.ext B x ETrm.id),
          by simp [tr, hA₀, hB], ReflTransGen.refl, eb BStep.beta⟩
      · simp at hA
  | @betaClos x m l nn =>
      intro M hM
      rcases tr_eq_app hM with ⟨A, B, rfl, hA, hB⟩ | ⟨A, B, rfl, hA, hB⟩
      · obtain ⟨A₀, L₀, hstepA, hA₀, hL₀⟩ := app_eps_preimage hA
        obtain ⟨A₁, rfl, hA₁⟩ := tr_eq_lam hA₀
        exact ⟨ETrm.comp A₁ (ETrm.ext B x L₀), ETrm.comp A₁ (ETrm.ext B x L₀),
          by simp [tr, hA₁, hB, hL₀], ReflTransGen.refl,
          ReflTransGen.trans (BSSteps.appL hstepA B) (eb BStep.betaClos)⟩
      · simp at hA
  | @stab m nn =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain ⟨A₁, rfl, hA₁⟩ := tr_eq_eps hA
      exact ⟨ETrm.eps A₁, ETrm.eps A₁, by simp [tr, hA₁], ReflTransGen.refl,
        ReflTransGen.trans hstep (es SStep.epsEps)⟩
  | @assoc l m nn =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain ⟨A₁, A₂, hstep2, hA₁, hA₂⟩ := app_eps_preimage hA
      exact ⟨ETrm.comp A₁ (ETrm.comp A₂ B), ETrm.comp A₁ (ETrm.comp A₂ B),
        by simp [tr, hA₁, hA₂, hB], ReflTransGen.refl,
        ReflTransGen.trans (ReflTransGen.trans hstep (BSSteps.compL hstep2 B))
          (es SStep.assoc)⟩
  | @idL m =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain rfl := tr_eq_id hA
      exact ⟨B, B, hB, ReflTransGen.refl, ReflTransGen.trans hstep (es SStep.idL)⟩
  | @idR m =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain rfl := tr_eq_id hB
      exact ⟨A, A, hA, ReflTransGen.refl, ReflTransGen.trans hstep (es SStep.idR)⟩
  | @dExt l x m nn =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain ⟨A₁, A₂, rfl, hA₁, hA₂⟩ := tr_eq_ext hA
      exact ⟨ETrm.ext (ETrm.comp A₁ B) x (ETrm.comp A₂ B),
        ETrm.ext (ETrm.comp A₁ B) x (ETrm.comp A₂ B),
        by simp [tr, hA₁, hA₂, hB], ReflTransGen.refl,
        ReflTransGen.trans hstep (es SStep.dExt)⟩
  | @varRef x m nn =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain rfl := tr_eq_var hA
      obtain ⟨B₁, B₂, rfl, hB₁, hB₂⟩ := tr_eq_ext hB
      exact ⟨B₁, B₁, hB₁, ReflTransGen.refl, ReflTransGen.trans hstep (es SStep.varRef)⟩
  | @varSkip x y m nn hxy =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain rfl := tr_eq_var hA
      obtain ⟨B₁, B₂, rfl, hB₁, hB₂⟩ := tr_eq_ext hB
      exact ⟨ETrm.comp (ETrm.var y) B₂, ETrm.comp (ETrm.var y) B₂,
        by simp [tr, hB₂], ReflTransGen.refl,
        ReflTransGen.trans hstep (es (SStep.varSkip hxy))⟩
  | @dApp m nn l =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      rcases tr_eq_app hA with ⟨A₁, A₂, rfl, hA₁, hA₂⟩ | ⟨A₁, A₂, rfl, hA₁, hA₂⟩
      · exact ⟨ETrm.app (ETrm.comp A₁ B) (ETrm.comp A₂ B),
          ETrm.app (ETrm.comp A₁ B) (ETrm.comp A₂ B),
          by simp [tr, hA₁, hA₂, hB], ReflTransGen.refl,
          ReflTransGen.trans hstep (es SStep.dApp)⟩
      · refine ⟨ETrm.app (ETrm.comp (ETrm.eps A₁) B) (ETrm.comp A₂ B),
          ETrm.comp A₁ (ETrm.comp A₂ B), ?_, ?_, ?_⟩
        · simp [tr, ← hA₁, hA₂, hB]
        · exact ReflTransGen.trans (BSSteps.appL (es SStep.epsEps) _) (eb BStep.compEps)
        · exact ReflTransGen.trans hstep (es SStep.assoc)
  | @const c m =>
      intro M hM
      obtain ⟨A, B, hstep, hA, hB⟩ := app_eps_preimage hM
      obtain rfl := tr_eq_const hA
      exact ⟨ETrm.const c, ETrm.const c, rfl, ReflTransGen.refl,
        ReflTransGen.trans hstep (es SStep.constC)⟩
  | @appL a a' b hstepF ih =>
      intro M hM
      rcases tr_eq_app hM with ⟨A, Bt, rfl, hA, hB⟩ | ⟨A, Bt, rfl, hA, hB⟩
      · obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih A hA
        exact ⟨ETrm.app N₀ Bt, ETrm.app L₀ Bt, by simp [tr, hN₀, hB],
          BSSteps.appL hNL Bt, BSSteps.appL hML Bt⟩
      · subst hA
        obtain ⟨a'', rfl, _⟩ := BetaSigmaStep.eps_inv hstepF
        obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih (ETrm.eps A) rfl
        obtain ⟨A₁, rfl, hAA₁⟩ := bsteps_eps_inv hML A rfl
        obtain ⟨N₁, rfl, hN₁⟩ := tr_eq_eps hN₀
        obtain ⟨A₂, hEq, hN₁A₂⟩ := bsteps_eps_inv hNL N₁ rfl
        injection hEq with hEq'
        subst hEq'
        exact ⟨ETrm.comp N₁ Bt, ETrm.comp A₁ Bt, by simp [tr, hN₁, hB],
          BSSteps.compL hN₁A₂ Bt, BSSteps.compL hAA₁ Bt⟩
  | @appR m m' l hstepF ih =>
      intro M hM
      rcases tr_eq_app hM with ⟨A, Bt, rfl, hA, hB⟩ | ⟨A, Bt, rfl, hA, hB⟩
      · obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih Bt hB
        exact ⟨ETrm.app A N₀, ETrm.app A L₀, by simp [tr, hA, hN₀],
          BSSteps.appR A hNL, BSSteps.appR A hML⟩
      · obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih Bt hB
        exact ⟨ETrm.comp A N₀, ETrm.comp A L₀, by simp [tr, hA, hN₀],
          BSSteps.compR A hNL, BSSteps.compR A hML⟩
  | @lam m m' x hstepF ih =>
      intro M hM
      obtain ⟨A, rfl, hA⟩ := tr_eq_lam hM
      obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih A hA
      exact ⟨ETrm.lam x N₀, ETrm.lam x L₀, by simp [tr, hN₀],
        BSSteps.lam hNL x, BSSteps.lam hML x⟩
  | @extL m m' x l hstepF ih =>
      intro M hM
      obtain ⟨A, Bt, rfl, hA, hB⟩ := tr_eq_ext hM
      obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih A hA
      exact ⟨ETrm.ext N₀ x Bt, ETrm.ext L₀ x Bt, by simp [tr, hN₀, hB],
        BSSteps.extL hNL x Bt, BSSteps.extL hML x Bt⟩
  | @extR m m' l x hstepF ih =>
      intro M hM
      obtain ⟨A, Bt, rfl, hA, hB⟩ := tr_eq_ext hM
      obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih Bt hB
      exact ⟨ETrm.ext A x N₀, ETrm.ext A x L₀, by simp [tr, hA, hN₀],
        BSSteps.extR A x hNL, BSSteps.extR A x hML⟩
  | @envAbst m m' hstepF ih =>
      intro M hM
      obtain ⟨A, rfl, hA⟩ := tr_eq_eps hM
      obtain ⟨N₀, L₀, hN₀, hNL, hML⟩ := ih A hA
      exact ⟨ETrm.eps N₀, ETrm.eps L₀, by simp [tr, hN₀],
        BSSteps.eps hNL, BSSteps.eps hML⟩

/-- **Multi-step lifting**, using confluence of `λ_EnvEps` to reconcile the
witnesses found along the chain. -/
theorem liftMulti {P Q : Trm V C} (h : BetaSigmaSteps P Q) :
    ∀ M : ETrm V C, tr M = P → ∃ N L, tr N = Q ∧ BSSteps N L ∧ BSSteps M L := by
  induction h with
  | refl => intro M hM; exact ⟨M, M, hM, ReflTransGen.refl, ReflTransGen.refl⟩
  | tail _ step ih =>
      intro M hM
      obtain ⟨N₀, L₀, hN₀, hNL₀, hML₀⟩ := ih M hM
      obtain ⟨N₁, L₁, hN₁, hNL₁, hN₀L₁⟩ := lift1 step N₀ hN₀
      obtain ⟨L₂, k₁, k₂⟩ := bsstep_confluent hNL₀ hN₀L₁
      exact ⟨N₁, L₂, hN₁, ReflTransGen.trans hNL₁ k₂, ReflTransGen.trans hML₀ k₁⟩

/-! ## Confluence of `λ_FREnv` -/

/-- **Confluence of the full beta/sigma reduction of `λ_FREnv`.** -/
theorem frenv_confluent : Confluent (BetaSigmaStep (V := V) (C := C)) := by
  intro P Q₁ Q₂ h₁ h₂
  obtain ⟨N₁, L₁, e₁, k₁, m₁⟩ := liftMulti h₁ (incl P) (tr_incl P)
  obtain ⟨N₂, L₂, e₂, k₂, m₂⟩ := liftMulti h₂ (incl P) (tr_incl P)
  obtain ⟨L, j₁, j₂⟩ := bsstep_confluent m₁ m₂
  refine ⟨tr L, ?_, ?_⟩
  · rw [← e₁]; exact tr_bssteps (ReflTransGen.trans k₁ j₁)
  · rw [← e₂]; exact tr_bssteps (ReflTransGen.trans k₂ j₂)

end LambdaFrenv
