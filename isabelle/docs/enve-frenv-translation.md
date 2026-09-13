# Translation from $\lambda_{\mathrm{Env}\varepsilon}$ to $\lambda_{\mathrm{FREnv}}$

This document describes the translation $⟦-⟧ : \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon}) \to \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, defined in thesis Definition 10 (§2.3.1, equation (2.12)).  The thesis calls this a "semantics" of $\lambda_{\mathrm{Env}\varepsilon}$ terms given in $\lambda_{\mathrm{FREnv}}$; here it is treated purely as a **translation** (a structural map between term sets), with no semantic/model-theoretic content implied.

> **Note for AI-assisted formalization.**
> This document is written to support formalization in Isabelle/HOL (or a
> similar proof assistant). It fixes constructor-level equations so that a
> language model or proof assistant can generate the translation function
> without guessing at bracket placement or recursion structure.

---

## 1  Source and Target Term Sets

- **Source**: $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, with constructors `Var`, `Id`, `App`, `Ext`, `Lam`, `Comp`, `Eps` -- see `docs/enve-syntax.md` §2.
- **Target**: $\mathbf{Term}(\lambda_{\mathrm{FREnv}})$, with constructors `Var`, `Lam`, `App`, `Id`, `Ext`, `Eps` -- see `docs/frenv-syntax.md` §2.

The two constructor sets are identical **except** that $\lambda_{\mathrm{Env}\varepsilon}$ has one extra constructor, `Comp` (environment composition, $M \circ N$), which $\lambda_{\mathrm{FREnv}}$ does not have. The translation $⟦-⟧$ is therefore the identity on every shared constructor, and eliminates `Comp` by rewriting it in terms of `Eps` and `App`.

---

## 2  Definition (Translation $⟦-⟧$)

The translation $⟦-⟧ : \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon}) \to \mathbf{Term}(\lambda_{\mathrm{FREnv}})$ is defined by structural recursion on the source term, using the following equations (thesis equation (2.12)). Here $x$ ranges over $\mathbf{Var}$ and $M, N$ range over $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$.

$$
\begin{aligned}
⟦x⟧ &= x \\
⟦\mathsf{id}⟧ &= \mathsf{id} \\
⟦\lambda x.\, M⟧ &= \lambda x.\, ⟦M⟧ \\
⟦M\,N⟧ &= ⟦M⟧\, ⟦N⟧ \\
⟦(M/x)\cdot N⟧ &= (⟦M⟧/x) \cdot ⟦N⟧ \\
⟦\varepsilon(M)⟧ &= \varepsilon(⟦M⟧) \\
⟦M \circ N⟧ &= \varepsilon(⟦M⟧)\, ⟦N⟧
\end{aligned}
$$

### 2.1  Constructor-Indexed Equation Table

| Source constructor | Equation | Target constructors used on the right |
| --- | --- | --- |
| `Var x` | $⟦x⟧ = x$ | `Var` |
| `Id` | $⟦\mathsf{id}⟧ = \mathsf{id}$ | `Id` |
| `Lam x M` | $⟦\lambda x.\,M⟧ = \lambda x.\, ⟦M⟧$ | `Lam` (recurse on body) |
| `App M N` | $⟦M\,N⟧ = ⟦M⟧\,⟦N⟧$ | `App` (recurse on both) |
| `Ext M x N` | $⟦(M/x)\cdot N⟧ = (⟦M⟧/x)\cdot ⟦N⟧$ | `Ext` (recurse on both) |
| `Eps M` | $⟦\varepsilon(M)⟧ = \varepsilon(⟦M⟧)$ | `Eps` (recurse on body) |
| `Comp M N` | $⟦M \circ N⟧ = \varepsilon(⟦M⟧)\,⟦N⟧$ | `Eps`, `App` (recurse on both, then combine) |

Six of the seven cases are pure homomorphisms: the source constructor is mapped to the identically-named target constructor, and the translation recurses into each subterm unchanged in shape. Only the `Comp` case is structurally different, since $\lambda_{\mathrm{FREnv}}$ has no constructor to receive it directly.

### 2.2  Suggested Isabelle/HOL Definition

Assuming `term` types `enve_term` (source, seven constructors) and `frenv_term` (target, six constructors) as declared in `enve-syntax.md` §2.2 and `frenv-syntax.md` §2.2 respectively:

```isabelle
fun translate :: "enve_term \<Rightarrow> frenv_term" ("\<lbrakk>_\<rbrakk>") where
  "\<lbrakk>Var x\<rbrakk>       = Var x"
| "\<lbrakk>Id\<rbrakk>          = Id"
| "\<lbrakk>Lam x M\<rbrakk>     = Lam x \<lbrakk>M\<rbrakk>"
| "\<lbrakk>App M N\<rbrakk>     = App \<lbrakk>M\<rbrakk> \<lbrakk>N\<rbrakk>"
| "\<lbrakk>Ext M x N\<rbrakk>   = Ext \<lbrakk>M\<rbrakk> x \<lbrakk>N\<rbrakk>"
| "\<lbrakk>Eps M\<rbrakk>       = Eps \<lbrakk>M\<rbrakk>"
| "\<lbrakk>Comp M N\<rbrakk>    = App (Eps \<lbrakk>M\<rbrakk>) \<lbrakk>N\<rbrakk>"
```

This function is total and structurally recursive (each right-hand side recurses only on strict subterms of the left-hand side pattern), so it is accepted by Isabelle's `fun` package without further termination proof obligations.

---

## 3  Why the `Comp` Case Looks the Way It Does

Recall from `enve-syntax.md` that in $\lambda_{\mathrm{Env}\varepsilon}$, an application headed by `Eps` reduces to `Comp` via the $\mathrm{Comp}_\varepsilon$ rule:

$$
\varepsilon(M)\,N \;\to\; M \circ N \qquad (\mathrm{Comp}_{\varepsilon}).
$$

The translation $⟦-⟧$ runs this correspondence in reverse at the level of raw syntax: since $\lambda_{\mathrm{FREnv}}$ has no primitive `Comp` former, a `Comp M N` node is translated back into the `App (Eps ...) ...` shape that would have produced it under $\mathrm{Comp}_{\varepsilon}$, i.e. $\varepsilon(⟦M⟧)\,⟦N⟧$. This is exactly what makes $⟦-⟧$ a *simulation* with respect to reduction (thesis Propositions 1-4, cited in `handoff-summary.md`): every $\sigma$/$\beta\sigma$ step available on $\mathrm{Comp}\,⟦M⟧\,⟦N⟧$-shaped $\lambda_{\mathrm{Env}\varepsilon}$ terms corresponds to an analogous step available on the `App (Eps ...) ...`-shaped $\lambda_{\mathrm{FREnv}}$ term it translates to, and vice versa.

---

## 4  Relationship to the Reverse Translation (§2.3.2, Definition 14)

The thesis also defines a map $f$ in the opposite direction, $f : \mathbf{Term}(\lambda_{\mathrm{FREnv}}) \to \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ (thesis Definition 14, equation (2.14)), which is the **trivial inclusion**: since every constructor of $\lambda_{\mathrm{FREnv}}$ already appears verbatim in $\lambda_{\mathrm{Env}\varepsilon}$ (all except `Comp`), $f$ simply maps each $\lambda_{\mathrm{FREnv}}$ constructor to its same-named counterpart, recursing homomorphically, with no case ever needing to introduce `Comp`. That map is **not** documented in this file; see `docs/frenv-enve-translation.md` if/when it is written up separately.

$⟦-⟧$ and $f$ are not mutually inverse in general: $⟦f(T)⟧ = T$ holds for every $T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$ (composing the inclusion with $⟦-⟧$ is the identity, since $f$ never produces a `Comp` node for $⟦-⟧$ to rewrite), but $f(⟦M⟧) = M$ does **not** hold in general for $M \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ containing `Comp`, since $⟦-⟧$ discards the `Comp` node in favor of an `App (Eps ...) ...` shape that $f$ then re-embeds literally rather than reconstructing the original `Comp`.
