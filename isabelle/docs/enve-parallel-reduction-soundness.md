# Soundness of Parallel Reduction with Respect to $\beta/\sigma$-Reduction

This document states and proves thesis Theorem 9 (§2.4.5), presented here as a **Lemma** as requested: every parallel-reduction step (`docs/enve-parallel-reduction.md`, thesis Definition 14) between $\sigma$-normal forms can be replayed as a (possibly longer) $\to_{\beta/\sigma}^{*}$-reduction (`docs/enve-beta-over-sigma-reduction.md`, thesis Definition 13). This is the converse direction to `docs/enve-parallel-reduction-simulation.md` (thesis Theorem 8): together, the two lemmas show $\Rightarrow_{\mathrm{par}}$ and $\to_{\beta/\sigma}^{*}$ reach exactly the same pairs of $\sigma$-normal forms.

> **Note for AI-assisted formalization.**
> The proof needs one auxiliary fact not stated elsewhere in this
> repository: that $\to_{\beta/\sigma}^{*}$ can be lifted through `Lam`,
> `Eps`, `App`, and `Ext` (the same four "safe" constructors identified in
> `docs/enve-beta-normal-form-simulation.md`), and, with a fixed
> `Lam`-headed or `Var`-headed partner, through `Comp` as well. This is
> stated below as the Fact, before the case analysis.

---

## Lemma (Soundness of Parallel Reduction)

Let $U$ be a $\sigma$-normal form of $\lambda_{\mathrm{Env}\varepsilon}$. If $U \Rightarrow_{\mathrm{par}} U'$, then $U \to_{\beta/\sigma}^{*} U'$.

#### Proof.

**Fact (context monotonicity of $\to_{\beta/\sigma}^{*}$).** If $P \to_{\beta/\sigma}^{*} P'$ (for $\sigma$-normal forms $P, P'$), then, for any fixed $\sigma$-normal form $Q$:
$$
\lambda x.\,P \to_{\beta/\sigma}^{*} \lambda x.\,P',
\qquad
\varepsilon(P) \to_{\beta/\sigma}^{*} \varepsilon(P'),
\qquad
P\,Q \to_{\beta/\sigma}^{*} P'\,Q,
\qquad
Q\,P \to_{\beta/\sigma}^{*} Q\,P',
$$
$$
(P/x)\cdot Q \to_{\beta/\sigma}^{*} (P'/x)\cdot Q,
\qquad
(Q/x)\cdot P \to_{\beta/\sigma}^{*} (Q/x)\cdot P'.
$$
This holds because each individual $\to_{\beta/\sigma}$-step making up $P \to_{\beta/\sigma}^{*} P'$ is, by Definition 13, a $\to_{\beta}$-step (which lifts through any of these four constructors, since $\to_{\beta}$ includes all congruence rules) followed by $\sigma$-normalization (which commutes with these four constructors, since none of `Lam`, `Eps`, `App`, `Ext` is ever a $\sigma$-redex, per the "safe context" observation of `docs/enve-beta-normal-form-simulation.md`); chaining the lifted single steps gives the lifted multi-step reduction. If, in addition, $Q$ is `Lam`-headed or `Var`-headed with the appropriate side condition ($Q \circ P \to^* Q \circ P'$ needs $P$'s replacement not to break the shape at the root -- but since $\Rightarrow_{\mathrm{par}}$ never turns a non-$\mathsf{id}$ term into $\mathsf{id}$ nor a non-environment-extension into one, as used below), the same lifting applies with `Comp` in place of the four constructors above, landing again on a $\sigma$-normal form.

The proof itself is by induction on the structure of $U$, case-split on the rule used last in the derivation of $U \Rightarrow_{\mathrm{par}} U'$.

**`ParId`.** $U = U' = \mathsf{id}$, so $U \to_{\beta/\sigma}^{*} U'$ in zero steps.

**`ParVar`.** $U = U' = x$, so $U \to_{\beta/\sigma}^{*} U'$ in zero steps.

**`ParLam`.** $U = \lambda x.\,U_1$, $U' = \lambda x.\,U_1'$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$. By the induction hypothesis, $U_1 \to_{\beta/\sigma}^{*} U_1'$. By the Fact, $U \to_{\beta/\sigma}^{*} \lambda x.\,U_1' = U'$.

**`ParEps`.** $U = \varepsilon(U_1)$, $U' = \varepsilon(U_1')$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$. By the induction hypothesis and the Fact: $U \to_{\beta/\sigma}^{*} \varepsilon(U_1') = U'$.

**`ParApp`.** $U = U_1 U_2$, $U' = U_1' U_2'$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$. By the induction hypothesis, $U_1 \to_{\beta/\sigma}^{*} U_1'$ and $U_2 \to_{\beta/\sigma}^{*} U_2'$. By the Fact (`AppL` then `AppR`): $U \to_{\beta/\sigma}^{*} U_1' U_2 \to_{\beta/\sigma}^{*} U_1' U_2' = U'$.

**`ParExtn`.** $U = (U_1/x)\cdot U_2$, $U' = (U_1'/x)\cdot U_2'$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$. By the induction hypothesis and the Fact (`ExtnL` then `ExtnR`): $U \to_{\beta/\sigma}^{*} (U_1'/x)\cdot U_2 \to_{\beta/\sigma}^{*} (U_1'/x)\cdot U_2' = U'$.

**`ParLamComp`.** $U = (\lambda x.\,U_1) \circ U_2$, $U' = \sigma((\lambda x.\,U_1') \circ U_2')$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$ (with $U_2 \neq \mathsf{id}$). By the induction hypothesis, $U_1 \to_{\beta/\sigma}^{*} U_1'$ and $U_2 \to_{\beta/\sigma}^{*} U_2'$. By the Fact (`Lam` then `CompL`, then `CompR` -- valid since $U_1$ was `Lam`-headed and $\Rightarrow_{\mathrm{par}}$ never changes that, and since $U_2 \neq \mathsf{id}$ is preserved by $\Rightarrow_{\mathrm{par}}$, because no rule of $\Rightarrow_{\mathrm{par}}$ produces $\mathsf{id}$ from a term other than $\mathsf{id}$ itself):
$$
U \to_{\beta/\sigma}^{*} (\lambda x.\,U_1') \circ U_2 \to_{\beta/\sigma}^{*} (\lambda x.\,U_1') \circ U_2'.
$$
Since $U_1'$ and $U_2'$ are $\sigma$-normal forms with $U_2' \neq \mathsf{id}$, $(\lambda x.\,U_1') \circ U_2'$ is already $\sigma$-normal, so $\sigma((\lambda x.\,U_1') \circ U_2') = (\lambda x.\,U_1') \circ U_2'$, giving $U \to_{\beta/\sigma}^{*} U'$ with no further step needed.

**`ParVarComp`.** $U = x \circ U_1$, $U' = \sigma(x \circ U_1')$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$ (with $U_1$ not an environment extension). By the induction hypothesis, $U_1 \to_{\beta/\sigma}^{*} U_1'$. By the Fact (`CompR`, valid since $\Rightarrow_{\mathrm{par}}$ never turns a non-environment-extension into one -- the only rule producing an environment extension, `ParExtn`, requires one as input): $U \to_{\beta/\sigma}^{*} x \circ U_1'$. Since $U_1'$ is a $\sigma$-normal form that is not an environment extension, $x \circ U_1'$ is already $\sigma$-normal, so $\sigma(x \circ U_1') = x \circ U_1' = U'$, giving $U \to_{\beta/\sigma}^{*} U'$ with no further step needed.

**`ParBeta`.** $U = (\lambda x.\,U_1)U_2$, $U' = \sigma(U_1' \circ ((U_2'/x)\cdot \mathsf{id}))$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$. By the induction hypothesis and the Fact (`AppL` then `AppR`): $U \to_{\beta/\sigma}^{*} (\lambda x.\,U_1')U_2 \to_{\beta/\sigma}^{*} (\lambda x.\,U_1')U_2'$. This last term is itself a `Beta` redex, so one further $\to_{\beta/\sigma}$-step gives $(\lambda x.\,U_1')U_2' \to_{\beta/\sigma} \sigma(U_1' \circ ((U_2'/x)\cdot \mathsf{id})) = U'$. Chaining, $U \to_{\beta/\sigma}^{*} U'$.

**`ParBetaClos`.** $U = ((\lambda x.\,U_1) \circ U_3)U_2$, $U' = \sigma(U_1' \circ ((U_2'/x)\cdot U_3'))$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U_3 \Rightarrow_{\mathrm{par}} U_3'$. By the induction hypothesis and the Fact (`Lam`/`CompL` for $U_1, U_3$, then `AppL`, then `AppR` for $U_2$): $U \to_{\beta/\sigma}^{*} ((\lambda x.\,U_1') \circ U_3')U_2 \to_{\beta/\sigma}^{*} ((\lambda x.\,U_1') \circ U_3')U_2'$. This last term is a `BetaClos` redex, so one further step gives $\to_{\beta/\sigma} \sigma(U_1' \circ ((U_2'/x)\cdot U_3')) = U'$. Chaining, $U \to_{\beta/\sigma}^{*} U'$.

**`ParComp$_\varepsilon$`.** $U = \varepsilon(U_1)U_2$, $U' = \sigma(U_1' \circ U_2')$, from $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$. By the induction hypothesis and the Fact (`Eps` then `AppL`, then `AppR`): $U \to_{\beta/\sigma}^{*} \varepsilon(U_1')U_2 \to_{\beta/\sigma}^{*} \varepsilon(U_1')U_2'$. This last term is a $\mathrm{Comp}_{\varepsilon}$ redex, so one further step gives $\to_{\beta/\sigma} \sigma(U_1' \circ U_2') = U'$. Chaining, $U \to_{\beta/\sigma}^{*} U'$.

This exhausts every rule by which $U \Rightarrow_{\mathrm{par}} U'$ could have been derived, so $U \to_{\beta/\sigma}^{*} U'$ holds whenever $U \Rightarrow_{\mathrm{par}} U'$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Context-monotonicity Fact made explicit.** The scanned source repeatedly writes steps such as "$U \to_{\beta/\sigma}^{*} \lambda x.\,U_1'$" directly from "$U_1 \to_{\beta/\sigma}^{*} U_1'$" without separately justifying that $\to_{\beta/\sigma}^{*}$ can be lifted through a surrounding constructor. This document states that lifting once, up front, as the Fact, and additionally verifies the two side conditions needed for the `Comp`-lifting case (`ParLamComp`/`ParVarComp`): that $\Rightarrow_{\mathrm{par}}$ never turns a non-$\mathsf{id}$ term into $\mathsf{id}$, and never turns a non-environment-extension into one, both by inspection of which rules of `docs/enve-parallel-reduction.md` could produce such an output.
- **No other changes.** Every other case matches the corresponding rule of `docs/enve-parallel-reduction.md` exactly, and each final $\sigma(-)$-wrapped target was checked to already be $\sigma$-normal (so that no extra reduction step is silently required beyond what is shown); no corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
- **`ParVarComp`'s single citation of the Fact expanded into a dedicated argument in the formalization.** The Fact as stated only covers a `Comp`-lifting step whose fixed `Var`-headed partner's environment argument stays clear of both $\mathsf{id}$ and environment-extension shape *throughout* the underlying $\to_{\beta/\sigma}^{*}$ chain, not just at its endpoints -- but $\Rightarrow_{\mathrm{par}}$ only guarantees this for the chain's endpoints ($W$, $W'$), not for any intermediate waypoint, and unlike $\mathsf{id}$ (a genuine dead end for $\to_{\beta/\sigma}$), becoming environment-extension-shaped mid-chain is not terminal. The Isabelle formalization (`EnvEps_Parallel_Reduction_Soundness.thy`) resolves this with a dedicated well-founded induction on the environment's size: at each step, either the change falls inside an `Ext`-shaped waypoint (handled via a new inversion lemma splitting into the `VarRef` sub-case -- where the change is either absorbed entirely, when it hits the discarded sub-tree, or transported directly -- and the `VarSkip` sub-case, which recurses on the strictly shorter environment tail) or it does not, in which case the fixed-partner composition is already $\sigma$-normal and lifts directly.
