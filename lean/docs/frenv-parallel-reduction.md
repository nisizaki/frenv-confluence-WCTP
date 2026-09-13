# Parallel Reduction for $\lambda_{\mathrm{FREnv}}$

This document describes the parallel-reduction infrastructure developed in
`LambdaFrenv/Par.lean` for the confluence proof of the beta-sigma reduction
$\to_{\beta\sigma}$ specified in `frenv-reduction-beta-sigma.md`.

## Purpose of `ParStep`

`ParStep M N` is the *parallel reduction* of $\lambda_{\mathrm{FREnv}}$: `N`
is obtained from `M` by reducing any finite, non-overlapping set of redexes
simultaneously.  It is the standard Tait–Martin-Löf parallel closure of the
one-step beta-sigma relation.

The relation has three groups of rules.

1. **Reflexivity.** `ParStep.refl : ParStep M M` — reducing no redex is a
   parallel step.

2. **Parallel congruence rules**, one for each syntactic form:
   - `ParStep.lam`  : `M ⇒ M'` implies `λx.M ⇒ λx.M'`;
   - `ParStep.app`  : `M ⇒ M'` and `N ⇒ N'` imply `(M N) ⇒ (M' N')`;
   - `ParStep.ext`  : `M ⇒ M'` and `N ⇒ N'` imply `((M/x)·N) ⇒ ((M'/x)·N')`;
   - `ParStep.eps`  : `M ⇒ M'` implies `ε(M) ⇒ ε(M')`.

3. **Parallel root rules**, one per beta-sigma root rule, in which every
   redex subterm is reduced simultaneously.  The name of each constructor
   matches its `BetaSigmaStep` counterpart:
   - `ParStep.beta`, `betaClos`, `stab`, `assoc`, `idL`, `idR`, `dExt`,
     `varRef`, `varSkip`, `dApp`, `const`.

For example, the parallel version of `dApp` is

```
dApp : ParStep M M' → ParStep N N' → ParStep L L' →
  ParStep (ε((M N)) L) ((ε(M')L') (ε(N')L'))
```

which reduces `M`, `N`, and `L` simultaneously and duplicates the reduct of
the environment argument `L`.

## Relationship to `BetaSigmaStep`

The one-step relation $\to_{\beta\sigma}$ and the parallel relation $\Rightarrow$
are equivalent up to the reflexive-transitive closure, via two verified theorems.

- **Embedding.** `ParStep.embed : BetaSigmaStep M N → ParStep M N`.
  Every one-step beta-sigma reduction is a single parallel step: instantiate
  the parallel root rule with `ParStep.refl` for every subterm, or apply the
  corresponding congruence rule for the compatibility rules.

- **Simulation.** `ParStep.sim : ParStep M N → BetaSigmaSteps M N`.
  Every parallel step is realized by a sequence of one-step beta-sigma
  reductions: reduce the subterms of each root redex one after another
  using the multi-step congruences, then fire the root rule.  The required
  multi-step congruences are proved as `BetaSigmaSteps.lam`, `.appL`, `.appR`,
  `.extL`, `.extR`, and `.eps`.

Together with reflexivity, these two theorems give

```
M →βσ N   iff   M ⇒ N
M →βσ* N  iff   M ⇒* N
```

in the sense that each relation is contained in the multi-step closure of the
other.

## Why parallel reduction?

Confluence of $\to_{\beta\sigma}$ is proved by showing that its parallel
closure $\Rightarrow$ is *strongly confluent* and then lifting strong
confluence to confluence of the reflexive-transitive closure.  Parallel
reduction makes the strong-confluence argument tractable because it
compresses an entire reduction "wave" into one step: the standard
induction on the two steps from a common source is much finer-grained for
$\Rightarrow$ than for the one-step relation, where a single source may be
simultaneously a redex at several nested positions.

The proof architecture is:

```
beta-sigma reduction (BetaSigmaStep)
    ↓  embed
parallel reduction (ParStep)
    ↓  strong confluence
confluence of ParStep
    ↓  sim
confluence of the reflexive-transitive closure of BetaSigmaStep
```

## Results proved in Lean

All in `LambdaFrenv/Par.lean` (file `LambdaFrenv/Par.lean`), verified by
`lake build`:

| Name | Statement |
| --- | --- |
| `ParStep.refl` | `ParStep M M` (constructor) |
| `BetaSigmaSteps.lam` | `M →* M'` implies `λx.M →* λx.M'` |
| `BetaSigmaSteps.appL` | `M →* M'` implies `(M N) →* (M' N)` |
| `BetaSigmaSteps.appR` | `N →* N'` implies `(M N) →* (M N')` |
| `BetaSigmaSteps.extL` | `M →* M'` implies `((M/x)·N) →* ((M'/x)·N)` |
| `BetaSigmaSteps.extR` | `N →* N'` implies `((M/x)·N) →* ((M/x)·N')` |
| `BetaSigmaSteps.eps` | `M →* M'` implies `ε(M) →* ε(M')` |
| `ParStep.embed` | `BetaSigmaStep M N` implies `ParStep M N` |
| `ParStep.sim` | `ParStep M N` implies `BetaSigmaSteps M N` |

Here `→*` abbreviates the reflexive-transitive closure `BetaSigmaSteps`.

## Remaining obligations for strong confluence

The target theorem is `ParStronglyConfluent`, i.e.
`StronglyConfluent ParStep`: from `M ⇒ N₁` and `M ⇒ N₂` one must find a
single term joining `N₁` and `N₂` by parallel steps.

A rule-by-rule overlap analysis of the root rules of `ParStep` identifies
the auxiliary *root-overlap join lemmas*.  The sources of the root rules are
all top-level applications `(f a)`; two distinct root rules can both fire on
one source only when their source patterns unify.

### Genuine root/root overlaps

1. **`assoc` against `dApp`** on `ε((ε(L)M))N` (`overlapAssocDApp`).
   `assoc` yields `ε(L')(ε(M')N')`; `dApp` yields
   `((ε(ε(L''))N'') (ε(M'')N''))`.  The join reduces the inner `ε(ε(L''))`
   by `stab`.

2. **`idR` overlaps** (`overlapIdRStab`, `overlapIdRIdL`, `overlapIdRConst`,
   `overlapIdRAssoc`, `overlapIdRExt`, `overlapIdRDApp`), on the sources
   `ε(ε(M))id`, `ε(id)id`, `ε(c)id`, `ε((ε(L)M))id`, `ε((L/x)·M)id`,
   `ε((MN))id`.  In each case the `idR` step reduces the whole body of the
   environment abstraction while the other rule reduces its subterms; the
   duplicated occurrences of the erased `id` are cancelled by further `idR`
   reductions.

3. **`varRef` and `varSkip`** on `(ε(z)((M/x)·N))` are mutually exclusive:
   `varRef` requires `z = x` and `varSkip` requires `z ≠ x`.  When either is
   combined with a parallel congruence step on the extension, the join is
   supplied by the induction hypothesis (`overlapVarRef`, `overlapVarSkip`).

### Structurally handled cases

- **`beta`/`betaClos` interactions.**  `beta` and `betaClos` never overlap
  at the root (their functions are `λx.M` and `(ε(λx.M)L)` respectively).
  Their interactions arise only at nested redex positions and are resolved
  by the congruence rules together with the induction hypothesis.
- **Duplication** by `dApp`, `dExt`, `betaClos`, and **erasure** by `idL`,
  `idR`, `varRef`, `const`, `stab`: when a root rule duplicates or erases a
  subterm that the other step reduces, the two copies are reduced
  consistently using the single-step joins obtained from the induction
  hypothesis.
- **Nested redexes** in general: when one step fires a root rule inside a
  subterm that the other step reduces at the root, the induction hypothesis
  is applied to the subterm.

Each obligation is stated in Lean as an unproved `Prop` (no axioms, no
`sorry`), so that the next milestone proves `ParStronglyConfluent` by
combining these lemmas.
