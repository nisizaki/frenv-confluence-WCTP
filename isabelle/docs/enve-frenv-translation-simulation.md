# Simulation of $\beta\sigma$-Reduction by the $\lambda_{\mathrm{Env}\varepsilon}$-to-$\lambda_{\mathrm{FREnv}}$ Translation

This document states and proves thesis Lemma 2 (§2.3.1): the translation $⟦-⟧ : \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon}) \to \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, defined in `docs/enve-frenv-translation.md` (thesis Definition 10), turns every one-step $\beta\sigma$-reduction of $\lambda_{\mathrm{Env}\varepsilon}$ into a (possibly zero-step) $\beta\sigma$-reduction of $\lambda_{\mathrm{FREnv}}$.

> **Note for AI-assisted formalization.**
> The proof is a single case analysis on which rule of $\to_{\beta\sigma}$
> (`docs/enve-reduction-beta-sigma.md`) was used to derive $M \to_{\beta\sigma} N$.
> Every case is checked the same way: unfold $⟦M⟧$ and $⟦N⟧$ using the
> equations of $⟦-⟧$ (`docs/enve-frenv-translation.md` §2), then match the
> result against a rule of $\lambda_{\mathrm{FREnv}}$'s own $\to_{\beta\sigma}$
> (`docs/frenv-reduction-beta-sigma.md`). No case requires guessing an
> intermediate term: each one is written out explicitly below.

---

## Lemma (Simulation of $\to_{\beta\sigma}$ by $⟦-⟧$)

For all $M, N \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\beta\sigma} N$ (in $\lambda_{\mathrm{Env}\varepsilon}$), then $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ (in $\lambda_{\mathrm{FREnv}}$).

#### Proof.

The proof is by case analysis on the rule of $\lambda_{\mathrm{Env}\varepsilon}$'s $\to_{\beta\sigma}$ (`docs/enve-reduction-beta-sigma.md`) used to derive $M \to_{\beta\sigma} N$. There are three groups of rules: beta rules, substitution rules, and congruence rules.

**Auxiliary fact (context monotonicity of $\to_{\beta\sigma}^{*}$).** Before the congruence-rule cases, we record a fact used repeatedly there: if $P \to_{\beta\sigma}^{*} P'$ in $\lambda_{\mathrm{FREnv}}$, then for every one-hole context $C[-]$ built from $\lambda_{\mathrm{FREnv}}$'s own congruence-rule positions (`Lam`, `AppL`/`AppR`, `ExtnL`/`ExtnR`, `EnvAbst`), $C[P] \to_{\beta\sigma}^{*} C[P']$. This holds because $\to_{\beta\sigma}^{*}$ is, by definition, the reflexive-transitive closure of $\to_{\beta\sigma}$: writing $P \to_{\beta\sigma}^{*} P'$ as a chain $P = P_0 \to_{\beta\sigma} P_1 \to_{\beta\sigma} \cdots \to_{\beta\sigma} P_k = P'$, applying the matching congruence rule of $\lambda_{\mathrm{FREnv}}$ to each link gives $C[P_0] \to_{\beta\sigma} C[P_1] \to_{\beta\sigma} \cdots \to_{\beta\sigma} C[P_k]$, i.e. $C[P] \to_{\beta\sigma}^{*} C[P']$.

### Beta rules

**Beta.** Here $M = (\lambda x.\,M_1)M_2$ and $N = M_1 \circ ((M_2/x)\cdot \mathsf{id})$.
$$
⟦M⟧ = ⟦(\lambda x.\,M_1)M_2⟧ = (\lambda x.\, ⟦M_1⟧)\,⟦M_2⟧.
$$
This is exactly a redex of $\lambda_{\mathrm{FREnv}}$'s `Beta` rule, $(\lambda x. P)Q \to_{\beta\sigma} \varepsilon(P)((Q/x)\cdot \mathsf{id})$, with $P = ⟦M_1⟧$, $Q = ⟦M_2⟧$. So
$$
⟦M⟧ \to_{\beta\sigma} \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot \mathsf{id}).
$$
On the other side,
$$
⟦N⟧ = ⟦M_1 \circ ((M_2/x)\cdot \mathsf{id})⟧ = \varepsilon(⟦M_1⟧)\,⟦(M_2/x)\cdot \mathsf{id}⟧ = \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot \mathsf{id}),
$$
which is the same term. Hence $⟦M⟧ \to_{\beta\sigma} ⟦N⟧$, so $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ in one step.

**BetaClos.** Here $M = ((\lambda x.\,M_1) \circ M_3)M_2$ and $N = M_1 \circ ((M_2/x)\cdot M_3)$.
$$
⟦M⟧ = ⟦((\lambda x.\,M_1) \circ M_3)M_2⟧ = (\varepsilon(\lambda x.\,⟦M_1⟧)\,⟦M_3⟧)\,⟦M_2⟧.
$$
This is exactly a redex of $\lambda_{\mathrm{FREnv}}$'s `BetaClos` rule, $((\varepsilon(\lambda x. P) L)Q \to_{\beta\sigma} \varepsilon(P)((Q/x)\cdot L)$, with $P = ⟦M_1⟧$, $L = ⟦M_3⟧$, $Q = ⟦M_2⟧$. So
$$
⟦M⟧ \to_{\beta\sigma} \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot ⟦M_3⟧).
$$
On the other side, $⟦N⟧ = \varepsilon(⟦M_1⟧)\,⟦(M_2/x)\cdot M_3⟧ = \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot ⟦M_3⟧)$, the same term. Hence $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ in one step.

**Comp** ($\mathrm{Comp}_{\varepsilon}$). Here $M = \varepsilon(M_1)M_2$ and $N = M_1 \circ M_2$.
$$
⟦M⟧ = ⟦\varepsilon(M_1)M_2⟧ = \varepsilon(⟦M_1⟧)\,⟦M_2⟧,
\qquad
⟦N⟧ = ⟦M_1 \circ M_2⟧ = \varepsilon(⟦M_1⟧)\,⟦M_2⟧.
$$
These are literally the same term (this is exactly the `Comp` equation of $⟦-⟧$ itself). So $⟦M⟧ = ⟦N⟧$, hence $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ in zero steps.

### Substitution rules

Each rule below decomposes $M_1 \circ M_2$ (for some subterms $M_1, M_2$) by the structure of $M_1$. In every case, $⟦M⟧$ unfolds to a redex of the correspondingly-named rule of $\lambda_{\mathrm{FREnv}}$, and reduces in exactly one $\to_{\beta\sigma}$ step to $⟦N⟧$.

**Assoc.** $M = (M_1 \circ M_2) \circ M_3$, $N = M_1 \circ (M_2 \circ M_3)$.
$$
⟦M⟧ = \varepsilon(⟦M_1 \circ M_2⟧)\,⟦M_3⟧ = \varepsilon(\varepsilon(⟦M_1⟧)\,⟦M_2⟧)\,⟦M_3⟧
\;\to_{\beta\sigma}^{\mathrm{Assoc}}\;
\varepsilon(⟦M_1⟧)(\varepsilon(⟦M_2⟧)\,⟦M_3⟧) = ⟦N⟧.
$$
(Using $\lambda_{\mathrm{FREnv}}$'s `Assoc`: $\varepsilon(\varepsilon(L)P)Q \to_{\beta\sigma} \varepsilon(L)(\varepsilon(P)Q)$.)

**IdL.** $M = \mathsf{id} \circ M_1$, $N = M_1$.
$$
⟦M⟧ = \varepsilon(⟦\mathsf{id}⟧)\,⟦M_1⟧ = \varepsilon(\mathsf{id})\,⟦M_1⟧
\;\to_{\beta\sigma}^{\mathrm{IdL}}\;
⟦M_1⟧ = ⟦N⟧.
$$

**IdR.** $M = M_1 \circ \mathsf{id}$, $N = M_1$.
$$
⟦M⟧ = \varepsilon(⟦M_1⟧)\,⟦\mathsf{id}⟧ = \varepsilon(⟦M_1⟧)\,\mathsf{id}
\;\to_{\beta\sigma}^{\mathrm{IdR}}\;
⟦M_1⟧ = ⟦N⟧.
$$

**DExtn.** $M = ((M_1/x)\cdot M_2) \circ M_3$, $N = ((M_1 \circ M_3)/x)\cdot(M_2 \circ M_3)$.
$$
⟦M⟧ = \varepsilon((⟦M_1⟧/x)\cdot⟦M_2⟧)\,⟦M_3⟧
\;\to_{\beta\sigma}^{\mathrm{DExtn}}\;
((\varepsilon(⟦M_1⟧)\,⟦M_3⟧)/x)\cdot(\varepsilon(⟦M_2⟧)\,⟦M_3⟧) = ⟦N⟧.
$$

**VarRef.** $M = x \circ ((M_1/x)\cdot M_2)$, $N = M_1$.
$$
⟦M⟧ = \varepsilon(x)((⟦M_1⟧/x)\cdot⟦M_2⟧)
\;\to_{\beta\sigma}^{\mathrm{VarRef}}\;
⟦M_1⟧ = ⟦N⟧.
$$

**VarSkip** ($x \neq y$). $M = x \circ ((M_1/y)\cdot M_2)$, $N = x \circ M_2$.
$$
⟦M⟧ = \varepsilon(x)((⟦M_1⟧/y)\cdot⟦M_2⟧)
\;\to_{\beta\sigma}^{\mathrm{VarSkip},\,x \neq y}\;
\varepsilon(x)\,⟦M_2⟧ = ⟦N⟧.
$$
(The side condition $x \neq y$ is on the variable *names*, which the translation never changes, so it transfers unchanged.)

**DApp.** $M = (M_1\,M_2) \circ M_3$, $N = (M_1 \circ M_3)(M_2 \circ M_3)$.
$$
⟦M⟧ = \varepsilon(⟦M_1⟧\,⟦M_2⟧)\,⟦M_3⟧
\;\to_{\beta\sigma}^{\mathrm{DApp}}\;
(\varepsilon(⟦M_1⟧)\,⟦M_3⟧)(\varepsilon(⟦M_2⟧)\,⟦M_3⟧) = ⟦N⟧.
$$

**Eps-eps.** $M = \varepsilon(M_1) \circ M_2$, $N = \varepsilon(M_1)$.
$$
⟦M⟧ = \varepsilon(⟦\varepsilon(M_1)⟧)\,⟦M_2⟧ = \varepsilon(\varepsilon(⟦M_1⟧))\,⟦M_2⟧
\;\to_{\beta\sigma}^{\mathrm{Eps\text{-}eps}}\;
\varepsilon(⟦M_1⟧) = ⟦N⟧.
$$
(Using $\lambda_{\mathrm{FREnv}}$'s nested-$\varepsilon$ rule `Eps-eps` from `docs/frenv-reduction-beta-sigma.md`: $\varepsilon(\varepsilon(P))Q \to_{\beta\sigma} \varepsilon(P)$.)

### Congruence rules

Each rule below has a premise $M_i \to_{\beta\sigma} N_i$ on a subterm. By the induction hypothesis (this lemma applied to the strictly smaller derivation of $M_i \to_{\beta\sigma} N_i$), $⟦M_i⟧ \to_{\beta\sigma}^{*} ⟦N_i⟧$. Combined with the auxiliary fact above (applied to the matching $\lambda_{\mathrm{FREnv}}$ congruence position), this gives $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ in each case, as follows.

**Lam.** $M = \lambda x.\,M_1$, $N = \lambda x.\,N_1$, from $M_1 \to_{\beta\sigma} N_1$.
By the induction hypothesis, $⟦M_1⟧ \to_{\beta\sigma}^{*} ⟦N_1⟧$. By context monotonicity under `Lam`, $\lambda x.\,⟦M_1⟧ \to_{\beta\sigma}^{*} \lambda x.\,⟦N_1⟧$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**Eop.** $M = \varepsilon(M_1)$, $N = \varepsilon(N_1)$, from $M_1 \to_{\beta\sigma} N_1$.
By the induction hypothesis and context monotonicity under `EnvAbst`, $\varepsilon(⟦M_1⟧) \to_{\beta\sigma}^{*} \varepsilon(⟦N_1⟧)$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**AppL.** $M = M_1 M_2$, $N = N_1 M_2$, from $M_1 \to_{\beta\sigma} N_1$.
By the induction hypothesis and context monotonicity under `AppL`, $⟦M_1⟧\,⟦M_2⟧ \to_{\beta\sigma}^{*} ⟦N_1⟧\,⟦M_2⟧$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**AppR.** $M = M_1 M_2$, $N = M_1 N_2$, from $M_2 \to_{\beta\sigma} N_2$.
By the induction hypothesis and context monotonicity under `AppR`, $⟦M_1⟧\,⟦M_2⟧ \to_{\beta\sigma}^{*} ⟦M_1⟧\,⟦N_2⟧$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**ExtnL.** $M = (M_1/x)\cdot M_2$, $N = (N_1/x)\cdot M_2$, from $M_1 \to_{\beta\sigma} N_1$.
By the induction hypothesis and context monotonicity under `ExtnL`, $(⟦M_1⟧/x)\cdot⟦M_2⟧ \to_{\beta\sigma}^{*} (⟦N_1⟧/x)\cdot⟦M_2⟧$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**ExtnR.** $M = (M_1/x)\cdot M_2$, $N = (M_1/x)\cdot N_2$, from $M_2 \to_{\beta\sigma} N_2$.
By the induction hypothesis and context monotonicity under `ExtnR`, $(⟦M_1⟧/x)\cdot⟦M_2⟧ \to_{\beta\sigma}^{*} (⟦M_1⟧/x)\cdot⟦N_2⟧$, i.e. $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$.

**CompL.** $M = M_1 \circ M_2$, $N = N_1 \circ M_2$, from $M_1 \to_{\beta\sigma} N_1$.
By the induction hypothesis, $⟦M_1⟧ \to_{\beta\sigma}^{*} ⟦N_1⟧$. Applying context monotonicity twice -- first under `EnvAbst` to get $\varepsilon(⟦M_1⟧) \to_{\beta\sigma}^{*} \varepsilon(⟦N_1⟧)$, then under `AppL` (with the fixed right argument $⟦M_2⟧$) -- gives
$$
⟦M⟧ = \varepsilon(⟦M_1⟧)\,⟦M_2⟧ \to_{\beta\sigma}^{*} \varepsilon(⟦N_1⟧)\,⟦M_2⟧ = ⟦N⟧.
$$

**CompR.** $M = M_1 \circ M_2$, $N = M_1 \circ N_2$, from $M_2 \to_{\beta\sigma} N_2$.
By the induction hypothesis and context monotonicity under `AppR` (with the fixed left argument $\varepsilon(⟦M_1⟧)$),
$$
⟦M⟧ = \varepsilon(⟦M_1⟧)\,⟦M_2⟧ \to_{\beta\sigma}^{*} \varepsilon(⟦M_1⟧)\,⟦N_2⟧ = ⟦N⟧.
$$

This exhausts all rules of $\lambda_{\mathrm{Env}\varepsilon}$'s $\to_{\beta\sigma}$, so $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ holds in every case.

#### End of Proof.

---

## Remark

This lemma is the one-step case of the broader simulation result mentioned in `handoff-summary.md` (the thesis's Propositions 1-4): that $⟦-⟧$ simulates *all* of $\lambda_{\mathrm{Env}\varepsilon}$'s reduction, not just single steps. The multi-step version, $M \to_{\beta\sigma}^{*} N \implies ⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$, follows from this lemma by an outer induction on the number of steps in $M \to_{\beta\sigma}^{*} N$: for zero steps, $M = N$ so $⟦M⟧ = ⟦N⟧$; for a chain $M \to_{\beta\sigma} M' \to_{\beta\sigma}^{*} N$, the lemma gives $⟦M⟧ \to_{\beta\sigma}^{*} ⟦M'⟧$, and the (shorter) chain $M' \to_{\beta\sigma}^{*} N$ gives $⟦M'⟧ \to_{\beta\sigma}^{*} ⟦N⟧$ by the induction hypothesis, and these two compose (by transitivity of $\to_{\beta\sigma}^{*}$) to $⟦M⟧ \to_{\beta\sigma}^{*} ⟦N⟧$. Together with the surjectivity of $⟦-⟧$ (`docs/enve-frenv-translation-surjective.md`), this is the sense in which $\lambda_{\mathrm{FREnv}}$-reduction is *simulated* by $\lambda_{\mathrm{Env}\varepsilon}$-reduction under $⟦-⟧$.
