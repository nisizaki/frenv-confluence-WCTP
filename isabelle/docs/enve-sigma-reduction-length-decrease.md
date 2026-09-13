# Length Decrease Under $\sigma$-Reduction on $\lambda_{\mathrm{Env}\varepsilon}$

This document states and proves thesis Theorem 3 (cited by the user as §2.3.1; its statement depends on the `length` measure of Definition 11, §2.4.1, `docs/enve-term-length-measure.md`), presented here as a **Lemma** as requested: every $\sigma$-reduction step on $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-reduction-sigma.md`) strictly decreases `length`. This is exactly the fact needed to show $\to_{\sigma}$ terminates (there is no infinite $\to_{\sigma}$-reduction sequence), since `length` takes values in the positive integers and cannot decrease forever.

> **Note for AI-assisted formalization.**
> The proof is a single case analysis on the last rule used to derive
> $M \to_{\sigma} N$, exactly mirroring the rule list of
> `docs/enve-reduction-sigma.md`. Every case reduces to elementary integer
> arithmetic once `length` is unfolded using the equations of
> `docs/enve-term-length-measure.md`; no case needs anything beyond that.

---

## Lemma (Length Decrease Under $\sigma$-Reduction)

For all $M, N \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\sigma} N$, then $\mathrm{length}(M) > \mathrm{length}(N)$.

#### Proof.

By induction on the structure of the derivation of $M \to_{\sigma} N$ (`docs/enve-reduction-sigma.md`), case-split on the rule used last. Throughout, `length` is unfolded using the equations of Definition 11 (`docs/enve-term-length-measure.md`).

### Substitution ($\sigma$-)rules

**`Assoc`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2, M_3$ with $M = (M_1 \circ M_2) \circ M_3$ and $N = M_1 \circ (M_2 \circ M_3)$. Writing $a = \mathrm{length}(M_1)$, $b = \mathrm{length}(M_2)$, $c = \mathrm{length}(M_3)$:
$$
\mathrm{length}(M) = \big(a(b+1)\big)(c+1),
\qquad
\mathrm{length}(N) = a\big(b(c+1)+1\big).
$$
Since $a \geq 1$, it suffices to show $(b+1)(c+1) > b(c+1)+1$, i.e. $(c+1) > 1$, which holds because $c = \mathrm{length}(M_3) \geq 1$. Hence $\mathrm{length}(M) > \mathrm{length}(N)$.

**`IdL`.** $M = \mathsf{id} \circ N$ for some $N$. $\mathrm{length}(M) = \mathrm{length}(\mathsf{id}) \cdot (\mathrm{length}(N) + 1) = \mathrm{length}(N) + 1 > \mathrm{length}(N)$.

**`IdR`.** $M = N \circ \mathsf{id}$ for some $N$. $\mathrm{length}(M) = \mathrm{length}(N) \cdot (\mathrm{length}(\mathsf{id}) + 1) = \mathrm{length}(N) \cdot 2 > \mathrm{length}(N)$, since $\mathrm{length}(N) \geq 1 > 0$.

**`DExtn`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2, M_3$ with $M = ((M_1/x)\cdot M_2) \circ M_3$ and $N = ((M_1 \circ M_3)/x)\cdot(M_2 \circ M_3)$. Writing $a = \mathrm{length}(M_1)$, $b = \mathrm{length}(M_2)$, $c = \mathrm{length}(M_3)$:
$$
\mathrm{length}(M) = (a + b + 1)(c + 1),
\qquad
\mathrm{length}(N) = a(c+1) + b(c+1) + 1 = (a+b)(c+1) + 1.
$$
The difference is $\mathrm{length}(M) - \mathrm{length}(N) = (c+1) - 1 = c \geq 1 > 0$. Hence $\mathrm{length}(M) > \mathrm{length}(N)$.

**`VarRef`.** There is a $\lambda_{\mathrm{Env}\varepsilon}$ term $M_1$ with $M = x \circ ((N/x)\cdot M_1)$. $\mathrm{length}(M) = \mathrm{length}(x) \cdot \big(\mathrm{length}((N/x)\cdot M_1) + 1\big) = 1 \cdot \big((\mathrm{length}(N) + \mathrm{length}(M_1) + 1) + 1\big) = \mathrm{length}(N) + \mathrm{length}(M_1) + 2 > \mathrm{length}(N)$.

**`VarSkip`** ($x \neq y$). There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2$ with $M = x \circ ((M_1/y)\cdot M_2)$ and $N = x \circ M_2$. $\mathrm{length}(M) = \mathrm{length}(M_1) + \mathrm{length}(M_2) + 2$ and $\mathrm{length}(N) = \mathrm{length}(M_2) + 1$ (both by the same unfolding as `VarRef`). So $\mathrm{length}(M) - \mathrm{length}(N) = \mathrm{length}(M_1) + 1 > 0$.

**`DApp`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2, M_3$ with $M = (M_1 M_2) \circ M_3$ and $N = (M_1 \circ M_3)(M_2 \circ M_3)$. Writing $a = \mathrm{length}(M_1)$, $b = \mathrm{length}(M_2)$, $c = \mathrm{length}(M_3)$:
$$
\mathrm{length}(M) = (a + b + 1)(c+1),
\qquad
\mathrm{length}(N) = a(c+1) + b(c+1) + 1 = (a+b)(c+1) + 1.
$$
This is the same pair of expressions as in the `DExtn` case, so $\mathrm{length}(M) - \mathrm{length}(N) = c \geq 1 > 0$.

**`Eps-eps`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2$ with $M = \varepsilon(M_1) \circ M_2$ and $N = \varepsilon(M_1)$. Writing $a = \mathrm{length}(M_1)$, $b = \mathrm{length}(M_2)$:
$$
\mathrm{length}(M) = \mathrm{length}(\varepsilon(M_1)) \cdot (\mathrm{length}(M_2) + 1) = 2a(b+1),
\qquad
\mathrm{length}(N) = \mathrm{length}(\varepsilon(M_1)) = 2a.
$$
Since $b \geq 1$, $b + 1 \geq 2$, so $\mathrm{length}(M) = 2a(b+1) \geq 4a > 2a = \mathrm{length}(N)$ (using $a \geq 1$). Hence $\mathrm{length}(M) > \mathrm{length}(N)$.

### Congruence rules

Each congruence rule case combines the induction hypothesis on the reduced subterm with the fact that every arithmetic operation appearing in Definition 11 (addition of a positive constant, multiplication by $2$, or multiplication by a factor $\geq 2$) is *strictly monotonic* in each argument. Concretely: if $p > q$ (both positive integers) and $k \geq 1$, then $p + k > q + k$ and $p \cdot k > q \cdot k$.

**`Lam`.** $M = \lambda x.\,M_1$, $N = \lambda x.\,N_1$, from $M_1 \to_{\sigma} N_1$. By the induction hypothesis, $\mathrm{length}(M_1) > \mathrm{length}(N_1)$. So $\mathrm{length}(M) = 2 \cdot \mathrm{length}(M_1) > 2 \cdot \mathrm{length}(N_1) = \mathrm{length}(N)$.

**`Eop`.** $M = \varepsilon(M_1)$, $N = \varepsilon(N_1)$, from $M_1 \to_{\sigma} N_1$. As for `Lam`: $\mathrm{length}(M) = 2 \cdot \mathrm{length}(M_1) > 2 \cdot \mathrm{length}(N_1) = \mathrm{length}(N)$.

**`AppL`.** $M = M_1 M_2$, $N = N_1 M_2$, from $M_1 \to_{\sigma} N_1$. By the induction hypothesis, $\mathrm{length}(M_1) > \mathrm{length}(N_1)$. So $\mathrm{length}(M) = \mathrm{length}(M_1) + \mathrm{length}(M_2) + 1 > \mathrm{length}(N_1) + \mathrm{length}(M_2) + 1 = \mathrm{length}(N)$.

**`AppR`.** $M = M_1 M_2$, $N = M_1 N_2$, from $M_2 \to_{\sigma} N_2$. Symmetric to `AppL`: $\mathrm{length}(M) = \mathrm{length}(M_1) + \mathrm{length}(M_2) + 1 > \mathrm{length}(M_1) + \mathrm{length}(N_2) + 1 = \mathrm{length}(N)$.

**`ExtnL`.** $M = (M_1/x)\cdot M_2$, $N = (N_1/x)\cdot M_2$, from $M_1 \to_{\sigma} N_1$. As for `AppL`: $\mathrm{length}(M) = \mathrm{length}(M_1) + \mathrm{length}(M_2) + 1 > \mathrm{length}(N_1) + \mathrm{length}(M_2) + 1 = \mathrm{length}(N)$.

**`ExtnR`.** $M = (M_1/x)\cdot M_2$, $N = (M_1/x)\cdot N_2$, from $M_2 \to_{\sigma} N_2$. As for `AppR`: $\mathrm{length}(M) = \mathrm{length}(M_1) + \mathrm{length}(M_2) + 1 > \mathrm{length}(M_1) + \mathrm{length}(N_2) + 1 = \mathrm{length}(N)$.

**`CompL`.** $M = M_1 \circ M_2$, $N = N_1 \circ M_2$, from $M_1 \to_{\sigma} N_1$. By the induction hypothesis, $\mathrm{length}(M_1) > \mathrm{length}(N_1)$, and $\mathrm{length}(M_2) + 1 \geq 2 > 0$, so multiplying preserves the strict inequality: $\mathrm{length}(M) = \mathrm{length}(M_1) \cdot (\mathrm{length}(M_2) + 1) > \mathrm{length}(N_1) \cdot (\mathrm{length}(M_2) + 1) = \mathrm{length}(N)$.

**`CompR`.** $M = M_1 \circ M_2$, $N = M_1 \circ N_2$, from $M_2 \to_{\sigma} N_2$. By the induction hypothesis, $\mathrm{length}(M_2) > \mathrm{length}(N_2)$, so $\mathrm{length}(M_2) + 1 > \mathrm{length}(N_2) + 1$, and $\mathrm{length}(M_1) \geq 1 > 0$, so multiplying preserves the strict inequality: $\mathrm{length}(M) = \mathrm{length}(M_1) \cdot (\mathrm{length}(M_2) + 1) > \mathrm{length}(M_1) \cdot (\mathrm{length}(N_2) + 1) = \mathrm{length}(N)$.

This exhausts every rule of $\to_{\sigma}$, so $\mathrm{length}(M) > \mathrm{length}(N)$ holds whenever $M \to_{\sigma} N$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **`Eps-eps` case corrected.** The scanned source computes $\mathrm{length}(M)$ for $M = \varepsilon(M_1) \circ M_2$ as $2 \cdot \mathrm{length}(M_1) + \mathrm{length}(M_2) + 1$, which does not match Definition 11's own equation for `Comp` ($\mathrm{length}(P \circ Q) = \mathrm{length}(P) \cdot (\mathrm{length}(Q) + 1)$, a **product**, not the sum shown). Applying that equation correctly with $P = \varepsilon(M_1)$, $Q = M_2$ gives $\mathrm{length}(M) = \mathrm{length}(\varepsilon(M_1)) \cdot (\mathrm{length}(M_2) + 1) = 2\,\mathrm{length}(M_1)\,(\mathrm{length}(M_2) + 1)$, which this document uses instead. The conclusion ($\mathrm{length}(M) > \mathrm{length}(N) = 2\,\mathrm{length}(M_1)$) still holds under the corrected computation, so the lemma itself is unaffected -- only the intermediate arithmetic in this one case was corrected to match Definition 11.
- **No other changes.** Every other case (`Assoc`, `IdL`, `IdR`, `DExtn`, `VarRef`, `VarSkip`, `DApp`, and all eight congruence rules) was checked against Definition 11's equations and found to unfold and simplify exactly as in the source; no further corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
