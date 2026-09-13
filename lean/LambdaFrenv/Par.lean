import LambdaFrenv.Basic

/-!
# Parallel reduction `ParStep` of λ_FREnv

This file develops the parallel-reduction infrastructure used to prove
confluence of `BetaSigmaStep`.

Parallel reduction `ParStep` performs, in a single parallel step, the
simultaneous reduction of a set of non-overlapping redexes.  It is the
standard Tait–Martin-Löf parallel closure of the beta-sigma reduction
`BetaSigmaStep`:

* a reflexivity rule `ParStep.refl`,
* parallel congruence rules for each syntactic form,
* a parallel version of each beta-sigma root rule, in which every
  redex subterm is reduced simultaneously.

The relationship to the one-step relation is:

* every one-step beta-sigma reduction is a parallel step
  (`ParStep.embed`),
* every parallel step is realized by a sequence of one-step beta-sigma
  reductions (`ParStep.sim`).

The main confluence proof uses parallel reduction because it satisfies
strong confluence, which then lifts to confluence of `BetaSigmaStep`.
-/

namespace LambdaFrenv

universe u v

/-- Parallel reduction on λ_FREnv terms.

`ParStep M N` means that `N` is obtained from `M` by reducing zero or more
(non-overlapping) redexes simultaneously.

The constructors mirror the beta-sigma rules of `BetaSigmaStep`, with the
following correspondence:

* `refl`        ↔ zero redexes
* `lam`, `app`, `ext`, `eps`  ↔ the parallel compatibility rules
* `beta`, `betaClos`, `stab`, `assoc`, `idL`, `idR`, `dExt`,
  `varRef`, `varSkip`, `dApp`, `const`
                ↔ the parallel versions of the beta-sigma root rules
-/
inductive ParStep : Trm V C → Trm V C → Prop where
  -- Reflexivity: zero redexes are reduced.
  | refl : ParStep M M
  -- λx.M ⇒ λx.M'  whenever  M ⇒ M'
  | lam : ParStep M M' →
      ParStep (Trm.lam x M) (Trm.lam x M')
  -- (M N) ⇒ (M' N')  whenever  M ⇒ M' and N ⇒ N'
  | app : ParStep M M' → ParStep N N' →
      ParStep (Trm.app M N) (Trm.app M' N')
  -- ((M/x)·N) ⇒ ((M'/x)·N')  whenever  M ⇒ M' and N ⇒ N'
  | ext : ParStep M M' → ParStep N N' →
      ParStep (Trm.ext M x N) (Trm.ext M' x N')
  -- ε(M) ⇒ ε(M')  whenever  M ⇒ M'
  | eps : ParStep M N →
      ParStep (Trm.eps M) (Trm.eps N)
  -- Beta: ((λx.M)N) ⇒ (ε(M')((N'/x)·id))  whenever M ⇒ M' and N ⇒ N'
  | beta : ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.lam x M) N)
        (Trm.app (Trm.eps M') (Trm.ext N' x Trm.id))
  -- BetaClos: ((ε(λx.M)L)N) ⇒ (ε(M')((N'/x)·L'))
  | betaClos : ParStep M M' → ParStep L L' → ParStep N N' →
      ParStep (Trm.app (Trm.app (Trm.eps (Trm.lam x M)) L) N)
        (Trm.app (Trm.eps M') (Trm.ext N' x L'))
  -- Stab: (ε(ε(M))N) ⇒ ε(M')
  | stab : ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.eps (Trm.eps M)) N) (Trm.eps M')
  -- Assoc: ε((ε(L)M))N ⇒ ε(L')(ε(M')N')
  | assoc : ParStep L L' → ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.eps (Trm.app (Trm.eps L) M)) N)
        (Trm.app (Trm.eps L') (Trm.app (Trm.eps M') N'))
  -- IdL: (ε(id)M) ⇒ M'
  | idL : ParStep M M' →
      ParStep (Trm.app (Trm.eps Trm.id) M) M'
  -- IdR: (ε(M)id) ⇒ M'
  | idR : ParStep M M' →
      ParStep (Trm.app (Trm.eps M) Trm.id) M'
  -- DExtn: (ε((L/x)·M)N) ⇒ ((ε(L')N')/x)·(ε(M')N')
  | dExt : ParStep L L' → ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.eps (Trm.ext L x M)) N)
        (Trm.ext (Trm.app (Trm.eps L') N') x (Trm.app (Trm.eps M') N'))
  -- VarRef: (ε(x)((M/x)·N)) ⇒ M'
  | varRef : ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.eps (Trm.var x)) (Trm.ext M x N)) M'
  -- VarSkip: x ≠ y ⇒ (ε(y)((M/x)·N)) ⇒ (ε(y)N')
  | varSkip : x ≠ y → ParStep M M' → ParStep N N' →
      ParStep (Trm.app (Trm.eps (Trm.var y)) (Trm.ext M x N))
        (Trm.app (Trm.eps (Trm.var y)) N')
  -- DApp: (ε((MN))L) ⇒ ((ε(M')L')(ε(N')L'))
  | dApp : ParStep M M' → ParStep N N' → ParStep L L' →
      ParStep (Trm.app (Trm.eps (Trm.app M N)) L)
        (Trm.app (Trm.app (Trm.eps M') L') (Trm.app (Trm.eps N') L'))
  -- Const: (ε(c)M) ⇒ c
  | const : ParStep M M' →
      ParStep (Trm.app (Trm.eps (Trm.const c)) M) (Trm.const c)

namespace BetaSigmaSteps

/-- λ-congruence of multi-step beta-sigma reduction. -/
theorem lam {M M' : Trm V C} (h : BetaSigmaSteps M M') (x : V) :
    BetaSigmaSteps (Trm.lam x M) (Trm.lam x M') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.lam hstep)

/-- Left application congruence of multi-step beta-sigma reduction. -/
theorem appL {M M' N : Trm V C} (h : BetaSigmaSteps M M') :
    BetaSigmaSteps (Trm.app M N) (Trm.app M' N) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.appL hstep)

/-- Right application congruence of multi-step beta-sigma reduction. -/
theorem appR {M N N' : Trm V C} (h : BetaSigmaSteps N N') :
    BetaSigmaSteps (Trm.app M N) (Trm.app M N') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.appR hstep)

/-- Left environment-extension congruence of multi-step beta-sigma reduction. -/
theorem extL {M M' N : Trm V C} (h : BetaSigmaSteps M M') (x : V) :
    BetaSigmaSteps (Trm.ext M x N) (Trm.ext M' x N) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.extL hstep)

/-- Right environment-extension congruence of multi-step beta-sigma reduction. -/
theorem extR {M N N' : Trm V C} (h : BetaSigmaSteps N N') (x : V) :
    BetaSigmaSteps (Trm.ext M x N) (Trm.ext M x N') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.extR hstep)

/-- Environment-abstraction congruence of multi-step beta-sigma reduction. -/
theorem eps {M N : Trm V C} (h : BetaSigmaSteps M N) :
    BetaSigmaSteps (Trm.eps M) (Trm.eps N) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (BetaSigmaStep.envAbst hstep)

end BetaSigmaSteps

namespace ParStep

/-- Embedding: every one-step beta-sigma reduction is a single parallel step. -/
theorem embed {M N : Trm V C} (h : BetaSigmaStep M N) : ParStep M N := by
  induction h with
  | beta => exact ParStep.beta ParStep.refl ParStep.refl
  | betaClos => exact ParStep.betaClos ParStep.refl ParStep.refl ParStep.refl
  | stab => exact ParStep.stab ParStep.refl ParStep.refl
  | assoc => exact ParStep.assoc ParStep.refl ParStep.refl ParStep.refl
  | idL => exact ParStep.idL ParStep.refl
  | idR => exact ParStep.idR ParStep.refl
  | dExt => exact ParStep.dExt ParStep.refl ParStep.refl ParStep.refl
  | varRef => exact ParStep.varRef ParStep.refl ParStep.refl
  | varSkip hneq => exact ParStep.varSkip hneq ParStep.refl ParStep.refl
  | dApp => exact ParStep.dApp ParStep.refl ParStep.refl ParStep.refl
  | const => exact ParStep.const ParStep.refl
  | appL h' ih => exact ParStep.app ih ParStep.refl
  | appR h' ih => exact ParStep.app ParStep.refl ih
  | lam h' ih => exact ParStep.lam ih
  | extL h' ih => exact ParStep.ext ih ParStep.refl
  | extR h' ih => exact ParStep.ext ParStep.refl ih
  | envAbst h' ih => exact ParStep.eps ih

/-- Simulation: every parallel step is realized by a sequence of one-step
beta-sigma reductions. -/
theorem sim {M N : Trm V C} (h : ParStep M N) : BetaSigmaSteps M N := by
  induction h with
  | refl => exact ReflTransGen.refl
  | lam h' ih => exact BetaSigmaSteps.lam ih _
  | app h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans (BetaSigmaSteps.appL ih1) (BetaSigmaSteps.appR ih2)
  | ext h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans (BetaSigmaSteps.extL ih1 _) (BetaSigmaSteps.extR ih2 _)
  | eps h' ih => exact BetaSigmaSteps.eps ih
  | beta h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans (BetaSigmaSteps.appL (BetaSigmaSteps.lam ih1 _)) (BetaSigmaSteps.appR ih2))
        (ReflTransGen.single BetaSigmaStep.beta)
  | betaClos h1 h2 h3 ih1 ih2 ih3 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans
          (ReflTransGen.trans
            (BetaSigmaSteps.appL (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.lam ih1 _))))
            (BetaSigmaSteps.appL (BetaSigmaSteps.appR ih2)))
          (BetaSigmaSteps.appR ih3))
        (ReflTransGen.single BetaSigmaStep.betaClos)
  | stab h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.eps ih1)))
          (BetaSigmaSteps.appR ih2))
        (ReflTransGen.single BetaSigmaStep.stab)
  | assoc h1 h2 h3 ih1 ih2 ih3 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans
          (ReflTransGen.trans
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.appL (BetaSigmaSteps.eps ih1))))
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.appR ih2))))
          (BetaSigmaSteps.appR ih3))
        (ReflTransGen.single BetaSigmaStep.assoc)
  | idL h' ih =>
      exact ReflTransGen.trans (BetaSigmaSteps.appR ih) (ReflTransGen.single BetaSigmaStep.idL)
  | idR h' ih =>
      exact ReflTransGen.trans (BetaSigmaSteps.appL (BetaSigmaSteps.eps ih)) (ReflTransGen.single BetaSigmaStep.idR)
  | dExt h1 h2 h3 ih1 ih2 ih3 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans
          (ReflTransGen.trans
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.extL ih1 _)))
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.extR ih2 _))))
          (BetaSigmaSteps.appR ih3))
        (ReflTransGen.single BetaSigmaStep.dExt)
  | varRef h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans (BetaSigmaSteps.appR (BetaSigmaSteps.extL ih1 _))
          (BetaSigmaSteps.appR (BetaSigmaSteps.extR ih2 _)))
        (ReflTransGen.single BetaSigmaStep.varRef)
  | varSkip hneq h1 h2 ih1 ih2 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans (BetaSigmaSteps.appR (BetaSigmaSteps.extL ih1 _))
          (BetaSigmaSteps.appR (BetaSigmaSteps.extR ih2 _)))
        (ReflTransGen.single (BetaSigmaStep.varSkip hneq))
  | dApp h1 h2 h3 ih1 ih2 ih3 =>
      exact ReflTransGen.trans
        (ReflTransGen.trans
          (ReflTransGen.trans
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.appL ih1)))
            (BetaSigmaSteps.appL (BetaSigmaSteps.eps (BetaSigmaSteps.appR ih2))))
          (BetaSigmaSteps.appR ih3))
        (ReflTransGen.single BetaSigmaStep.dApp)
  | const h' ih =>
      exact ReflTransGen.trans (BetaSigmaSteps.appR ih) (ReflTransGen.single BetaSigmaStep.const)

end ParStep

/-! ## Strong-confluence obligations

Strong confluence of `ParStep` — `StronglyConfluent ParStep` — is the
subject of the next milestone.  Its proof requires, beyond the structural
cases handled by the induction hypothesis, a family of *root-overlap join
lemmas*: cases in which two parallel steps from a common source both apply
root rules at the root.

A rule-by-rule analysis of the root rules of `ParStep` shows that the only
genuine root/root overlaps (two distinct root rules whose source patterns
unify) are:

* `assoc` against `dApp`, on the source `ε((ε(L)M))N`;
* `idR` against each of `stab`, `idL`, `const`, `assoc`, `dExt`, `dApp`,
  on the sources `ε(ε(M))id`, `ε(id)id`, `ε(c)id`, `ε((ε(L)M))id`,
  `ε((L/x)·M)id`, `ε((MN))id`;
* `varRef` against `varSkip`, which are mutually exclusive by the side
  condition `x ≠ y`.

The remaining hard cases (`beta`/`betaClos` interactions, duplication by
`dApp`/`dExt`/`betaClos`, erasure by `idL`/`idR`/`varRef`/`const`/`stab`,
and nested redexes) arise structurally and are resolved by the congruence
rules together with the induction hypothesis.

Each obligation below is stated (but not yet proved) in full generality
over the simultaneous subterm reductions.  `ParJoinable` is multi-step
joinability under `ParStep`; the strong-confluence proof will instantiate
the subterm steps with single parallel steps and their single-step joins.
-/

/-- Multi-step parallel reduction, `M ⇒* N`. -/
abbrev ParSteps {V : Type u} {C : Type v} (M N : Trm V C) : Prop :=
  ReflTransGen ParStep M N

/-- Joinability under parallel reduction: `M` and `N` have a common
parallel-reduction reduct. -/
def ParJoinable {V : Type u} {C : Type v} (M N : Trm V C) : Prop :=
  ∃ L : Trm V C, ParSteps M L ∧ ParSteps N L

/-- Strong confluence of parallel reduction.  This is the main theorem
of the strong-confluence milestone. -/
def ParStronglyConfluent {V : Type u} {C : Type v} : Prop :=
  StronglyConfluent (ParStep (V := V) (C := C))

/-- `assoc`/`dApp` root overlap: the sources `ε((ε(L)M))N` match both
rules; the two reducts must join. -/
def overlapAssocDApp {V : Type u} {C : Type v} : Prop :=
  ∀ {L M N L₁ M₁ N₁ M₂ N₂ L₂ : Trm V C},
    ParStep L L₁ → ParStep M M₁ → ParStep N N₁ →
    ParStep (Trm.eps L) M₂ → ParStep M N₂ → ParStep N L₂ →
    ParJoinable (Trm.app (Trm.eps L₁) (Trm.app (Trm.eps M₁) N₁))
      (Trm.app (Trm.app (Trm.eps M₂) L₂) (Trm.app (Trm.eps N₂) L₂))

/-- `idR`/`stab` root overlap on `ε(ε(M))id`: the `idR` step reduces
`ε(M)` while `stab` reduces the inner `M`. -/
def overlapIdRStab {V : Type u} {C : Type v} : Prop :=
  ∀ {M M₁ M₂ : Trm V C},
    ParStep (Trm.eps M) M₁ → ParStep M M₂ →
    ParJoinable M₁ (Trm.eps M₂)

/-- `idR`/`idL` root overlap on `ε(id)id`; both sides are reflexively
joinable. -/
def overlapIdRIdL {V : Type u} {C : Type v} : Prop :=
  ∀ {M₁ M₂ : Trm V C}, ParStep Trm.id M₁ → ParStep Trm.id M₂ →
    ParJoinable M₁ M₂

/-- `idR`/`const` root overlap on `ε(c)id`; both sides reduce to `c`. -/
def overlapIdRConst {V : Type u} {C : Type v} : Prop :=
  ∀ {c : C} {M₁ M₂ : Trm V C},
    ParStep (Trm.const c) M₁ → ParStep Trm.id M₂ →
    ParJoinable M₁ (Trm.const c)

/-- `idR`/`assoc` root overlap on `ε((ε(L)M))id`; the `idR` step reduces
the whole `ε(L)M` while `assoc` reduces `L`, `M` and the erased `id`. -/
def overlapIdRAssoc {V : Type u} {C : Type v} : Prop :=
  ∀ {L M L₂ M₂ N₂ A₁ : Trm V C},
    ParStep (Trm.app (Trm.eps L) M) A₁ →
    ParStep L L₂ → ParStep M M₂ → ParStep Trm.id N₂ →
    ParJoinable A₁ (Trm.app (Trm.eps L₂) (Trm.app (Trm.eps M₂) N₂))

/-- `idR`/`dExt` root overlap on `ε((L/x)·M)id`; the `idR` step reduces
the whole `(L/x)·M` while `dExt` distributes `id` through the extension. -/
def overlapIdRExt {V : Type u} {C : Type v} : Prop :=
  ∀ {L M : Trm V C} {x : V} {L₂ M₂ N₂ A₁ : Trm V C},
    ParStep (Trm.ext L x M) A₁ →
    ParStep L L₂ → ParStep M M₂ → ParStep Trm.id N₂ →
    ParJoinable A₁ (Trm.ext (Trm.app (Trm.eps L₂) N₂) x (Trm.app (Trm.eps M₂) N₂))

/-- `idR`/`dApp` root overlap on `ε((MN))id`; the `idR` step reduces the
whole `MN` while `dApp` distributes `id` over the application. -/
def overlapIdRDApp {V : Type u} {C : Type v} : Prop :=
  ∀ {M N M₂ N₂ L₂ A₁ : Trm V C},
    ParStep (Trm.app M N) A₁ →
    ParStep M M₂ → ParStep N N₂ → ParStep Trm.id L₂ →
    ParJoinable A₁ (Trm.app (Trm.app (Trm.eps M₂) L₂) (Trm.app (Trm.eps N₂) L₂))

/-- `varRef` against a congruence step on `(ε(x)((M/x)·N))`: the extension
reduces simultaneously while `varRef` returns the value bound to `x`. -/
def overlapVarRef {V : Type u} {C : Type v} : Prop :=
  ∀ {x : V} {M N M₁ N₁ M₂ N₂ : Trm V C},
    ParStep M M₁ → ParStep N N₁ →
    ParStep M M₂ → ParStep N N₂ →
    ParJoinable M₁ (Trm.app (Trm.eps (Trm.var x)) (Trm.ext M₂ x N₂))

/-- `varSkip` against a congruence step on `(ε(y)((M/x)·N))` with `x ≠ y`:
the extension reduces while `varSkip` skips the binding. -/
def overlapVarSkip {V : Type u} {C : Type v} : Prop :=
  ∀ {x y : V} {M N M₁ N₁ M₂ N₂ : Trm V C},
    x ≠ y →
    ParStep M M₁ → ParStep N N₁ →
    ParStep M M₂ → ParStep N N₂ →
    ParJoinable (Trm.app (Trm.eps (Trm.var y)) N₁)
      (Trm.app (Trm.eps (Trm.var y)) (Trm.ext M₂ x N₂))

end LambdaFrenv
