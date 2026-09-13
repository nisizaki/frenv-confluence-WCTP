# Surjectivity of the $\lambda_{\mathrm{Env}\varepsilon}$-to-$\lambda_{\mathrm{FREnv}}$ Translation

This document states and proves thesis Lemma 1 (§2.3.1): the translation $⟦-⟧ : \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon}) \to \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, defined in `docs/enve-frenv-translation.md` (thesis Definition 10, equation (2.12)), is a **surjective** map.

> **Note for AI-assisted formalization.**
> This document is self-contained: it restates the auxiliary map `f` it
> needs (thesis Definition 14, §2.3.2) inline, so a language model or proof
> assistant does not need to consult another file to check the proof step
> by step.

---

## Auxiliary Construction: the Inclusion $f$

The proof below uses a map $f : \mathbf{Term}(\lambda_{\mathrm{FREnv}}) \to \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ (thesis Definition 14, equation (2.14)), defined by structural recursion:

$$
\begin{aligned}
f(x) &= x \\
f(\mathsf{id}) &= \mathsf{id} \\
f(\lambda x.\, M) &= \lambda x.\, f(M) \\
f(M\,N) &= f(M)\, f(N) \\
f((M/x)\cdot N) &= (f(M)/x) \cdot f(N) \\
f(\varepsilon(M)) &= \varepsilon(f(M))
\end{aligned}
$$

Every constructor of $\lambda_{\mathrm{FREnv}}$ (`Var`, `Lam`, `App`, `Id`, `Ext`, `Eps`) already occurs, with the same name and arity, among the constructors of $\lambda_{\mathrm{Env}\varepsilon}$ (`Var`, `Id`, `App`, `Ext`, `Lam`, `Comp`, `Eps`) -- see `docs/frenv-syntax.md` §2 and `docs/enve-syntax.md` §2. So $f$ is simply the constructor-preserving inclusion of $\lambda_{\mathrm{FREnv}}$-terms into $\lambda_{\mathrm{Env}\varepsilon}$-terms: it recurses on every subterm and never has to produce a `Comp` node, because `Comp` never appears on the left-hand side of any of its defining equations.

---

## Lemma (Surjectivity of $⟦-⟧$)

For every $T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, there exists $M \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ such that $⟦M⟧ = T$.

#### Proof.

Fix $T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$. Take $M = f(T)$, using the map $f$ defined above. It suffices to show

$$
⟦f(T)⟧ = T \qquad \text{for every } T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}}),
$$

by structural induction on $T$.

Since $T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, its head constructor is one of `Var`, `Lam`, `App`, `Id`, `Ext`, `Eps` -- it is never `Comp`, because $\lambda_{\mathrm{FREnv}}$ has no `Comp` constructor. So the case analysis has exactly six cases, and in each case the defining equation for $f$ (above) and the corresponding equation for $⟦-⟧$ (`docs/enve-frenv-translation.md` §2, thesis equation (2.12)) line up constructor-for-constructor:

- **`Var x`.** $⟦f(x)⟧ = ⟦x⟧ = x$.

- **`Id`.** $⟦f(\mathsf{id})⟧ = ⟦\mathsf{id}⟧ = \mathsf{id}$.

- **`Lam x M_1`.** By the induction hypothesis, $⟦f(M_1)⟧ = M_1$. Then
  $$
  ⟦f(\lambda x.\, M_1)⟧ = ⟦\lambda x.\, f(M_1)⟧ = \lambda x.\, ⟦f(M_1)⟧ = \lambda x.\, M_1.
  $$

- **`App M_1 M_2`.** By the induction hypothesis, $⟦f(M_1)⟧ = M_1$ and $⟦f(M_2)⟧ = M_2$. Then
  $$
  ⟦f(M_1\,M_2)⟧ = ⟦f(M_1)\, f(M_2)⟧ = ⟦f(M_1)⟧\, ⟦f(M_2)⟧ = M_1\, M_2.
  $$

- **`Ext M_1\ x\ M_2`.** By the induction hypothesis, $⟦f(M_1)⟧ = M_1$ and $⟦f(M_2)⟧ = M_2$. Then
  $$
  ⟦f((M_1/x)\cdot M_2)⟧ = ⟦(f(M_1)/x) \cdot f(M_2)⟧ = (⟦f(M_1)⟧/x) \cdot ⟦f(M_2)⟧ = (M_1/x) \cdot M_2.
  $$

- **`Eps M_1`.** By the induction hypothesis, $⟦f(M_1)⟧ = M_1$. Then
  $$
  ⟦f(\varepsilon(M_1))⟧ = ⟦\varepsilon(f(M_1))⟧ = \varepsilon(⟦f(M_1)⟧) = \varepsilon(M_1).
  $$

There is no seventh case for `Comp`, since $f$'s domain $\mathbf{Term}(\lambda_{\mathrm{FREnv}})$ contains no `Comp`-headed term; in particular, the `Comp`-elimination equation $⟦M \circ N⟧ = \varepsilon(⟦M⟧)\,⟦N⟧$ of $⟦-⟧$ is never invoked in this proof.

This covers all cases, so $⟦f(T)⟧ = T$ holds for every $T \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$ by structural induction. Taking $M = f(T)$ therefore exhibits, for the arbitrary $T$ fixed at the start, an $M \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ with $⟦M⟧ = T$. Hence $⟦-⟧$ is surjective.

#### End of Proof.

---

## Remark

The lemma shows more than bare surjectivity: it shows that $f$ is a **right inverse** (a section) of $⟦-⟧$, i.e. $⟦-⟧ \circ f = \mathrm{id}_{\mathbf{Term}(\lambda_{\mathrm{FREnv}})}$. The reverse composite $f \circ ⟦-⟧$ is *not* the identity on $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ -- for instance $f(⟦M \circ N⟧) = f(\varepsilon(⟦M⟧)\,⟦N⟧) = \varepsilon(f(⟦M⟧))\,f(⟦N⟧)$, which is an `App (Eps ...) ...` term, not the original `Comp M N` term, whenever $M \circ N$ actually occurs. So $⟦-⟧$ is surjective but not injective: $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ is "larger" than $\mathbf{Term}(\lambda_{\mathrm{FREnv}})$ only in the sense of containing distinct `Comp`-headed terms that all collapse onto the same `App (Eps ...) ...`-shaped image under $⟦-⟧$. This point is already noted, from the opposite direction, in `docs/enve-frenv-translation.md` §4.
