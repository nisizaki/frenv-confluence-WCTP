# Local Confluence of $\sigma$-Reduction on $\lambda_{\mathrm{Env}\varepsilon}$

This document states and proves thesis Lemma 5 (§2.4.2), presented here as a **Theorem** as requested: the $\sigma$-reduction relation $\to_{\sigma}$ on $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-reduction-sigma.md`) is locally confluent.

> **Note for AI-assisted formalization.**
> The proof method is the standard critical-pair method also used in
> `docs/frenv-beta-sigma-local-confluence.md`: a peak $N_1 \leftarrow M \to_{\sigma} N_2$
> either uses the same rule at the same position (trivial), uses two rules
> at disjoint positions (commutes automatically via the congruence rules),
> or uses two rules whose left-hand sides overlap -- a **critical pair**,
> of which there are only finitely many since $\to_{\sigma}$'s eight rules
> (`Assoc`, `IdL`, `IdR`, `DExtn`, `VarRef`, `VarSkip`, `DApp`, `Eps-eps`)
> all have fixed, finite left-hand-side patterns. Every critical pair is
> checked individually below.

---

## Theorem (Local Confluence of $\sigma$-Reduction)

For all $M, N_1, N_2 \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\sigma} N_1$ and $M \to_{\sigma} N_2$, then there exists $L \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ such that $N_1 \to_{\sigma}^{*} L$ and $N_2 \to_{\sigma}^{*} L$.

#### Proof.

As in `docs/frenv-beta-sigma-local-confluence.md`, a peak $N_1 \leftarrow M \to_{\sigma} N_2$ falls into one of three cases.

**Same rule, same position.** Every rule of $\to_{\sigma}$ is deterministic (its left-hand side determines its right-hand side uniquely, and `VarRef`/`VarSkip` are mutually exclusive by their side conditions), so if both steps use the same rule at the same position, $N_1 = N_2$ and $L := N_1$ works with zero further steps.

**Disjoint positions.** If the two redexes occur in non-overlapping subterms of $M$, the congruence rules of $\to_{\sigma}$ (`Lam`, `Eop`, `AppL`, `AppR`, `ExtnL`, `ExtnR`, `CompL`, `CompR`) let each reduction be performed independently inside the other's result, reaching a common $L$ that has both reductions applied. This is a general, rule-independent fact about context-based rewriting, not checked separately below.

**Overlapping positions (critical pairs).** This is the substantial case: one redex position is a prefix of the other, or the same term matches two rules' patterns at once. Because all eight rules of $\to_{\sigma}$ decompose a term headed by `Comp` (i.e. of the form $P \circ Q$) by inspecting the shape of $P$ (and, for `IdR`, of $Q$), the only overlaps possible are between two rules whose patterns both constrain the shape of an *outer* `Comp` node's left argument in a way that a `Comp`-shaped or `Id`-shaped subterm can satisfy simultaneously. Checking every pair of the eight rules exhaustively for such an overlap yields exactly eleven critical pairs, corresponding to thesis equations (2.21)-(2.31); every other pair of rules has no overlapping instance at all, because their left-hand-side patterns constrain incompatible shapes (e.g. `DExtn` needs $P$ to be `Ext`-headed while `VarRef`/`VarSkip` need $P$ to be `Var`-headed -- no single term can be both). Each of the eleven is joinable, as follows.

### (2.21) `Assoc` / `Assoc`

Peak: $((M_1 \circ M_2) \circ M_3) \circ M_4$.

$$
((M_1 \circ M_2) \circ M_3) \circ M_4
\xrightarrow{\mathrm{Assoc}} (M_1 \circ (M_2 \circ M_3)) \circ M_4
\xrightarrow{\mathrm{Assoc}} M_1 \circ ((M_2 \circ M_3) \circ M_4)
\xrightarrow{\mathrm{Assoc}} M_1 \circ (M_2 \circ (M_3 \circ M_4))
$$
$$
((M_1 \circ M_2) \circ M_3) \circ M_4
\xrightarrow{\mathrm{Assoc}} (M_1 \circ M_2) \circ (M_3 \circ M_4)
\xrightarrow{\mathrm{Assoc}} M_1 \circ (M_2 \circ (M_3 \circ M_4))
$$

Both routes reach $M_1 \circ (M_2 \circ (M_3 \circ M_4))$.

### (2.22) `IdL` / `Assoc`

Peak: $(\mathsf{id} \circ M_1) \circ M_2$.

$$
(\mathsf{id} \circ M_1) \circ M_2 \xrightarrow{\mathrm{IdL}} M_1 \circ M_2
$$
$$
(\mathsf{id} \circ M_1) \circ M_2 \xrightarrow{\mathrm{Assoc}} \mathsf{id} \circ (M_1 \circ M_2) \xrightarrow{\mathrm{IdL}} M_1 \circ M_2
$$

Both routes reach $M_1 \circ M_2$.

### (2.23) `IdR` / `Assoc`

There are two instances, according to whether the $\mathsf{id}$ sits at the innermost left or the innermost right position of the peak.

$$
(M_1 \circ \mathsf{id}) \circ M_2 \xrightarrow{\mathrm{IdR}} M_1 \circ M_2
$$
$$
(M_1 \circ \mathsf{id}) \circ M_2 \xrightarrow{\mathrm{Assoc}} M_1 \circ (\mathsf{id} \circ M_2) \xrightarrow{\mathrm{IdL}} M_1 \circ M_2
$$

$$
(M_1 \circ M_2) \circ \mathsf{id} \xrightarrow{\mathrm{IdR}} M_1 \circ M_2
$$
$$
(M_1 \circ M_2) \circ \mathsf{id} \xrightarrow{\mathrm{Assoc}} M_1 \circ (M_2 \circ \mathsf{id}) \xrightarrow{\mathrm{IdR}} M_1 \circ M_2
$$

Both instances join at $M_1 \circ M_2$.

### (2.24) `IdR` / `IdL`

Peak: $\mathsf{id} \circ \mathsf{id}$.

$$
\mathsf{id} \circ \mathsf{id} \xrightarrow{\mathrm{IdR}} \mathsf{id}
\qquad\qquad
\mathsf{id} \circ \mathsf{id} \xrightarrow{\mathrm{IdL}} \mathsf{id}
$$

Both routes reach $\mathsf{id}$.

### (2.25) `DExtn` / `IdR`

Peak: $((M_1/x)\cdot M_2) \circ \mathsf{id}$.

$$
((M_1/x)\cdot M_2) \circ \mathsf{id}
\xrightarrow{\mathrm{DExtn}} ((M_1 \circ \mathsf{id})/x)\cdot(M_2 \circ \mathsf{id})
\xrightarrow{\mathrm{IdR}} (M_1/x)\cdot(M_2 \circ \mathsf{id})
\xrightarrow{\mathrm{IdR}} (M_1/x)\cdot M_2
$$
$$
((M_1/x)\cdot M_2) \circ \mathsf{id} \xrightarrow{\mathrm{IdR}} (M_1/x)\cdot M_2
$$

Both routes reach $(M_1/x)\cdot M_2$.

### (2.26) `VarRef` / `Assoc`

Peak: $(x \circ ((M_1/x)\cdot M_2)) \circ M_3$.

$$
(x \circ ((M_1/x)\cdot M_2)) \circ M_3 \xrightarrow{\mathrm{VarRef}} M_1 \circ M_3
$$
$$
(x \circ ((M_1/x)\cdot M_2)) \circ M_3
\xrightarrow{\mathrm{Assoc}} x \circ (((M_1/x)\cdot M_2) \circ M_3)
\xrightarrow{\mathrm{DExtn}} x \circ (((M_1 \circ M_3)/x)\cdot(M_2 \circ M_3))
\xrightarrow{\mathrm{VarRef}} M_1 \circ M_3
$$

Both routes reach $M_1 \circ M_3$.

### (2.27) `VarSkip` / `Assoc`

Peak: $(x \circ ((M_1/y)\cdot M_2)) \circ M_3$, with $x \neq y$.

$$
(x \circ ((M_1/y)\cdot M_2)) \circ M_3
\xrightarrow{\mathrm{VarSkip}} (x \circ M_2) \circ M_3
\xrightarrow{\mathrm{Assoc}} x \circ (M_2 \circ M_3)
$$
$$
(x \circ ((M_1/y)\cdot M_2)) \circ M_3
\xrightarrow{\mathrm{Assoc}} x \circ (((M_1/y)\cdot M_2) \circ M_3)
\xrightarrow{\mathrm{DExtn}} x \circ (((M_1 \circ M_3)/y)\cdot(M_2 \circ M_3))
\xrightarrow{\mathrm{VarSkip}} x \circ (M_2 \circ M_3)
$$

Both routes reach $x \circ (M_2 \circ M_3)$.

### (2.28) `DApp` / `Assoc`

Peak: $((M_1 M_2) \circ M_3) \circ M_4$.

$$
((M_1 M_2) \circ M_3) \circ M_4
\xrightarrow{\mathrm{DApp}} ((M_1 \circ M_3)(M_2 \circ M_3)) \circ M_4
\xrightarrow{\mathrm{DApp}} ((M_1 \circ M_3) \circ M_4)((M_2 \circ M_3) \circ M_4)
\xrightarrow{\mathrm{Assoc}} (M_1 \circ (M_3 \circ M_4))((M_2 \circ M_3) \circ M_4)
\xrightarrow{\mathrm{Assoc}} (M_1 \circ (M_3 \circ M_4))(M_2 \circ (M_3 \circ M_4))
$$
$$
((M_1 M_2) \circ M_3) \circ M_4
\xrightarrow{\mathrm{Assoc}} (M_1 M_2) \circ (M_3 \circ M_4)
\xrightarrow{\mathrm{DApp}} (M_1 \circ (M_3 \circ M_4))(M_2 \circ (M_3 \circ M_4))
$$

Both routes reach $(M_1 \circ (M_3 \circ M_4))(M_2 \circ (M_3 \circ M_4))$.

### (2.29) `DApp` / `IdR`

Peak: $(M_1 M_2) \circ \mathsf{id}$.

$$
(M_1 M_2) \circ \mathsf{id}
\xrightarrow{\mathrm{DApp}} (M_1 \circ \mathsf{id})(M_2 \circ \mathsf{id})
\xrightarrow{\mathrm{IdR}} M_1(M_2 \circ \mathsf{id})
\xrightarrow{\mathrm{IdR}} M_1 M_2
$$
$$
(M_1 M_2) \circ \mathsf{id} \xrightarrow{\mathrm{IdR}} M_1 M_2
$$

Both routes reach $M_1 M_2$.

### (2.30) `Eps-eps` / `Assoc`

Peak: $(\varepsilon(M_1) \circ M_2) \circ M_3$.

$$
(\varepsilon(M_1) \circ M_2) \circ M_3
\xrightarrow{\mathrm{Eps\text{-}eps}} \varepsilon(M_1) \circ M_3
\xrightarrow{\mathrm{Eps\text{-}eps}} \varepsilon(M_1)
$$
$$
(\varepsilon(M_1) \circ M_2) \circ M_3
\xrightarrow{\mathrm{Assoc}} \varepsilon(M_1) \circ (M_2 \circ M_3)
\xrightarrow{\mathrm{Eps\text{-}eps}} \varepsilon(M_1)
$$

Both routes reach $\varepsilon(M_1)$.

### (2.31) `Eps-eps` / `IdR`

Peak: $\varepsilon(M_1) \circ \mathsf{id}$.

$$
\varepsilon(M_1) \circ \mathsf{id} \xrightarrow{\mathrm{Eps\text{-}eps}} \varepsilon(M_1)
\qquad\qquad
\varepsilon(M_1) \circ \mathsf{id} \xrightarrow{\mathrm{IdR}} \varepsilon(M_1)
$$

Both routes reach $\varepsilon(M_1)$.

### Assembling the theorem

Every peak $N_1 \leftarrow M \to_{\sigma} N_2$ falls into the same-rule case, the disjoint-position case, or one of the eleven critical pairs above, each of which was shown joinable. Hence a common $L$ with $N_1 \to_{\sigma}^{*} L$ and $N_2 \to_{\sigma}^{*} L$ always exists, which is exactly local confluence of $\to_{\sigma}$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **One mislabeled step corrected.** In the first instance of critical pair (2.23) ($( M_1 \circ \mathsf{id}) \circ M_2$), the scanned source labels the step $\mathsf{id} \circ M_2 \to M_2$ as an application of `IdR`. That step's left-hand side, $\mathsf{id} \circ M_2$, matches `IdL` ($\mathsf{id} \circ M \to M$), not `IdR` ($M \circ \mathsf{id} \to M$); this document labels it `IdL` instead. The joined term ($M_1 \circ M_2$) is unaffected by this correction.
- **No other changes.** All eleven critical pairs, and the "no overlap" (`*`) entries of the source's Table 2.3 for every other pair of the eight $\sigma$-rules, were checked and found consistent; no further corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
