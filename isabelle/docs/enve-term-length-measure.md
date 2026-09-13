# Length Measure on $\lambda_{\mathrm{Env}\varepsilon}$ Terms

This document records thesis Definition 11 (§2.4.1, equation (2.20)): a function `length` from $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ to the positive integers, defined by structural recursion. The thesis uses it later as a decreasing measure to prove termination of the $\sigma$-rules (`docs/enve-reduction-sigma.md`).

> **Note for AI-assisted formalization.**
> `length` is defined by a single equation per constructor of
> $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ (`docs/enve-syntax.md`
> §2.2: `Var`, `Id`, `App`, `Ext`, `Lam`, `Comp`, `Eps`), each right-hand
> side depending only on the `length` of strict subterms. This makes it a
> textbook structurally-recursive function, straightforward to translate
> directly into an Isabelle/HOL `fun` definition without guessing at
> termination obligations.

---

#### Definition (Term Length Measure)

The function $\mathrm{length} : \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon}) \to \mathbb{Z}^{+}$ is defined by structural recursion, for $x \in \mathbf{Var}$ and $M, N \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, as follows (thesis equation (2.20)):

$$
\begin{aligned}
\mathrm{length}(\mathsf{id}) &= 1 \\
\mathrm{length}(x) &= 1 \\
\mathrm{length}(M\,N) &= \mathrm{length}(M) + \mathrm{length}(N) + 1 \\
\mathrm{length}((M/x)\cdot N) &= \mathrm{length}(M) + \mathrm{length}(N) + 1 \\
\mathrm{length}(\lambda x.\,M) &= 2 \cdot \mathrm{length}(M) \\
\mathrm{length}(\varepsilon(M)) &= 2 \cdot \mathrm{length}(M) \\
\mathrm{length}(M \circ N) &= \mathrm{length}(M) \cdot (\mathrm{length}(N) + 1)
\end{aligned}
$$

### Constructor-Indexed Equation Table

| Constructor | Equation | Depends on |
| --- | --- | --- |
| `Id` | $\mathrm{length}(\mathsf{id}) = 1$ | (base case) |
| `Var x` | $\mathrm{length}(x) = 1$ | (base case) |
| `App M N` | $\mathrm{length}(M\,N) = \mathrm{length}(M) + \mathrm{length}(N) + 1$ | $\mathrm{length}(M)$, $\mathrm{length}(N)$ |
| `Ext M x N` | $\mathrm{length}((M/x)\cdot N) = \mathrm{length}(M) + \mathrm{length}(N) + 1$ | $\mathrm{length}(M)$, $\mathrm{length}(N)$ |
| `Lam x M` | $\mathrm{length}(\lambda x.\,M) = 2 \cdot \mathrm{length}(M)$ | $\mathrm{length}(M)$ |
| `Eps M` | $\mathrm{length}(\varepsilon(M)) = 2 \cdot \mathrm{length}(M)$ | $\mathrm{length}(M)$ |
| `Comp M N` | $\mathrm{length}(M \circ N) = \mathrm{length}(M) \cdot (\mathrm{length}(N) + 1)$ | $\mathrm{length}(M)$, $\mathrm{length}(N)$ |

Every case covers exactly one of the seven constructors of $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ (`docs/enve-syntax.md` §2.1), and every right-hand side refers only to the `length` of strict subterms of the left-hand side's argument(s), so this is a total, well-founded (structurally recursive) definition: `length` is defined on every term, by recursion on term size.

### Positivity

$\mathrm{length}(M) \geq 1$ for every $M$, by induction on $M$: the two base cases give exactly $1$; `App` and `Ext` give a sum of two values $\geq 1$ plus $1$, so $\geq 3$; `Lam` and `Eps` give twice a value $\geq 1$, so $\geq 2$; and `Comp` gives a product of a value $\geq 1$ and a value $\geq 2$ (since $\mathrm{length}(N) + 1 \geq 2$), so $\geq 2$. Hence `length` indeed takes values in the positive integers $\mathbb{Z}^{+}$, as the thesis states.

### Suggested Isabelle/HOL Definition

Using the `term` datatype for $\lambda_{\mathrm{Env}\varepsilon}$ from `docs/enve-syntax.md` §2.2:

```isabelle
fun length_enve :: "term \<Rightarrow> nat" where
  "length_enve Id            = 1"
| "length_enve (Var x)       = 1"
| "length_enve (App M N)     = length_enve M + length_enve N + 1"
| "length_enve (Ext M x N)   = length_enve M + length_enve N + 1"
| "length_enve (Lam x M)     = 2 * length_enve M"
| "length_enve (Eps M)       = 2 * length_enve M"
| "length_enve (Comp M N)    = length_enve M * (length_enve N + 1)"
```

(Isabelle's `nat` starts at $0$, not $1$; the positivity fact above -- `length_enve M > 0` for all `M` -- would need to be stated and proved as a separate lemma by structural induction, rather than being built into the type as it is when informally writing $\mathbb{Z}^{+}$.)

---

## Remarks and Adjustments Made to the Source Material

- **No `Const` case.** $\lambda_{\mathrm{Env}\varepsilon}$ has no constant symbols and no `Const` constructor (`docs/enve-syntax.md`), so `length` here has exactly the seven cases above, one per constructor, and no `Const` case was added or removed -- the source material for this definition did not include one to begin with.
- **No other changes.** The seven equations above are a direct transcription of thesis equation (2.20); no correction was needed. The "Positivity" and "Suggested Isabelle/HOL Definition" sections are added for this document's stated purpose (support formalization) and were not present in the thesis text itself.
