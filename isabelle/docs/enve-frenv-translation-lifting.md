# Single-Step Lifting Lemma for the $\lambda_{\mathrm{Env}\varepsilon}$-to-$\lambda_{\mathrm{FREnv}}$ Translation

This document states and proves thesis Lemma 3 (§2.3.1): every single $\beta\sigma$-step out of the *translated* term $⟦M⟧$ can be matched, on the $\lambda_{\mathrm{Env}\varepsilon}$ side, by an explicit reduction of $M$ itself, landing on a term whose translation is exactly that step's target. This is the converse direction to the Simulation Lemma (`docs/enve-frenv-translation-simulation.md`, thesis Lemma 2): Lemma 2 pushes $\lambda_{\mathrm{Env}\varepsilon}$-side steps forward through $⟦-⟧$; this lemma pulls a single $\lambda_{\mathrm{FREnv}}$-side step back.

> **Revision note.** An earlier version of this document, titled "Postponement Lemma", reconstructed a different (and, on inspection, unprovable-as-stated) claim from illegible scanned source material, and relied on citing local confluence of $\lambda_{\mathrm{FREnv}}$'s $\to_{\beta\sigma}$ (`docs/frenv-beta-sigma-local-confluence.md`). Having now reviewed a clear transcription of the thesis's actual proof, this document replaces that reconstruction entirely. **The real Lemma 3 does not need confluence, local confluence, or any other joinability fact at all** -- its proof is a direct, constructive case analysis that exhibits the needed $\lambda_{\mathrm{Env}\varepsilon}$-side reduction by hand in every case, using only the rules of `docs/enve-reduction-beta-sigma.md`.

---

## Lemma (Single-Step Lifting Lemma)

Let $M$ be a term of $\lambda_{\mathrm{Env}\varepsilon}$ and $N'$ a term of $\lambda_{\mathrm{FREnv}}$. If $⟦M⟧ \to_{\beta\sigma} N'$, then there exist $\lambda_{\mathrm{Env}\varepsilon}$ terms $N, L$ such that
$$
⟦N⟧ = N',
\qquad
N \to_{\beta\sigma}^{*} L,
\qquad
M \to_{\beta\sigma}^{*} L.
$$

Informally: whatever single $\lambda_{\mathrm{FREnv}}$-side step $⟦M⟧$ takes, its target $N'$ is exactly the translation of some $\lambda_{\mathrm{Env}\varepsilon}$ term $N$ that is joinable with $M$ *entirely on the $\lambda_{\mathrm{Env}\varepsilon}$ side* -- $N$ and $M$ both reduce (in $\lambda_{\mathrm{Env}\varepsilon}$) to a common term $L$.

#### Proof.

By induction on the structure of the derivation of $⟦M⟧ \to_{\beta\sigma} N'$, case-split on the rule of $\lambda_{\mathrm{FREnv}}$'s $\to_{\beta\sigma}$ (`docs/frenv-reduction-beta-sigma.md`) used last.

Two of $\lambda_{\mathrm{Env}\varepsilon}$'s own reduction rules (`docs/enve-reduction-beta-sigma.md`) are used repeatedly below and are worth naming up front:

- **Comp$_\varepsilon$**: $\varepsilon(P)\,Q \to_{\beta\sigma} P \circ Q$.
- Each $\sigma$-rule (`Assoc`, `IdL`, `IdR`, `DExtn`, `VarRef`, `VarSkip`, `DApp`, `Eps-eps`) decomposes $P \circ Q$ by the shape of $P$, exactly mirroring the corresponding rule of $\lambda_{\mathrm{FREnv}}$.

A recurring pattern in the base-rule cases below is this: because $⟦\varepsilon(P)⟧ = \varepsilon(⟦P⟧)$ and $⟦P \circ Q⟧ = \varepsilon(⟦P⟧)\,⟦Q⟧$ **give the same translation**, a $\lambda_{\mathrm{FREnv}}$ term of the shape $\varepsilon(P')\,Q'$ has (at least) two possible $\lambda_{\mathrm{Env}\varepsilon}$ preimages at that position: a literal $\varepsilon(P)\,Q$ (plain application) or a $P \circ Q$ (composition). Both are handled uniformly: from $P \circ Q$, one $\mathrm{Comp}_\varepsilon^{-1}$-free step is saved, while from $\varepsilon(P)\,Q$, firing `Comp$_\varepsilon$` first reduces it to $P \circ Q$, after which both cases proceed identically.

### Base rules

**`Beta`.** $⟦M⟧ \to_{\beta\sigma} N'$ was derived by `Beta`, so there are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2$ with $M = (\lambda x.\,M_1)M_2$, $⟦M⟧ = (\lambda x.\,⟦M_1⟧)\,⟦M_2⟧$, and $N' = \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot \mathsf{id})$.

Set $N := M_1 \circ ((M_2/x)\cdot \mathsf{id})$ and $L := N$. Then $⟦N⟧ = \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot \mathsf{id}) = N'$; $N \to_{\beta\sigma}^{*} L$ holds trivially (zero steps, $N = L$); and $M \to_{\beta\sigma} L$ holds in one step, since $M = (\lambda x.\,M_1)M_2 \to_{\beta\sigma}^{\mathrm{Beta}} M_1 \circ ((M_2/x)\cdot \mathsf{id}) = L$ is exactly $\lambda_{\mathrm{Env}\varepsilon}$'s own `Beta` rule.

**`BetaClos`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_1, M_2$ (with $M_3$ already fixed as part of $M$'s own shape) such that $M = ((\lambda x.\,M_1) \circ M_3)M_2$, $⟦M⟧ = (\varepsilon(\lambda x.\,⟦M_1⟧)\,⟦M_3⟧)\,⟦M_2⟧$, and $N' = \varepsilon(⟦M_1⟧)((⟦M_2⟧/x)\cdot ⟦M_3⟧)$.

Set $N := L := M_1 \circ ((M_2/x)\cdot M_3)$. Then $⟦N⟧ = N'$; $N \to_{\beta\sigma}^{*} L$ is zero steps; and $M \to_{\beta\sigma} L$ in one step by $\lambda_{\mathrm{Env}\varepsilon}$'s own `BetaClos` rule.

**`Assoc`.** $⟦M⟧ = \varepsilon(\varepsilon(⟦M_1⟧)\,⟦M_2⟧)\,⟦M_3⟧$ and $N' = \varepsilon(⟦M_1⟧)(\varepsilon(⟦M_2⟧)\,⟦M_3⟧)$, and $M$ is one of the following four shapes (all four translate to the same $⟦M⟧$, because $⟦P \circ Q⟧ = ⟦\varepsilon(P)\,Q⟧$):
$$
M = (M_1 \circ M_2) \circ M_3,
\quad
M = (\varepsilon(M_1)M_2) \circ M_3,
\quad
M = \varepsilon(M_1 \circ M_2)\,M_3,
\quad
M = \varepsilon(\varepsilon(M_1)M_2)\,M_3.
$$

In every case, set $N := L := M_1 \circ (M_2 \circ M_3)$; then $⟦N⟧ = N'$ and $N \to_{\beta\sigma}^{*} L$ is zero steps. For $M \to_{\beta\sigma}^{*} L$: the first shape reaches $L$ in one `Assoc` step directly; the second and third shapes first fire `Comp$_\varepsilon$` once (on the $\varepsilon(M_1)M_2$ or $\varepsilon(M_1 \circ M_2)$ part, respectively) to reach the first shape's intermediate term, then fire `Assoc`; the fourth shape fires `Comp$_\varepsilon$` twice (once to strip each of the two $\varepsilon(-)$-applications down to a $\circ$) before firing `Assoc`.

**`IdL`.** $⟦M⟧ = \varepsilon(\mathsf{id})\,⟦M_1⟧$, $N' = ⟦M_1⟧$, and $M = \mathsf{id} \circ M_1$ or $M = \varepsilon(\mathsf{id})M_1$. Set $N := L := M_1$. Then $⟦N⟧ = N'$, $N \to_{\beta\sigma}^{*} L$ is zero steps, and $M \to_{\beta\sigma}^{*} L$ is one `IdL` step (first shape) or `Comp$_\varepsilon$` then `IdL` (second shape).

**`IdR`.** $⟦M⟧ = \varepsilon(⟦M_1⟧)\,\mathsf{id}$, $N' = ⟦M_1⟧$, and $M = M_1 \circ \mathsf{id}$ or $M = \varepsilon(M_1)\,\mathsf{id}$. Set $N := L := M_1$; symmetric to `IdL`.

**`DExtn`.** $⟦M⟧ = \varepsilon((⟦M_1⟧/x)\cdot⟦M_2⟧)\,⟦M_3⟧$, $N' = ((\varepsilon(⟦M_1⟧)⟦M_3⟧)/x)\cdot(\varepsilon(⟦M_2⟧)⟦M_3⟧)$, and $M = ((M_1/x)\cdot M_2) \circ M_3$ or $M = \varepsilon((M_1/x)\cdot M_2)\,M_3$. Set $N := L := ((M_1 \circ M_3)/x)\cdot(M_2 \circ M_3)$. Then $⟦N⟧ = N'$; $M \to_{\beta\sigma}^{*} L$ is one `DExtn` step (first shape) or `Comp$_\varepsilon$` then `DExtn` (second shape).

**`VarRef`.** $⟦M⟧ = \varepsilon(x)((⟦M_1⟧/x)\cdot⟦M_2⟧)$, $N' = ⟦M_1⟧$, and $M = x \circ ((M_1/x)\cdot M_2)$ or $M = \varepsilon(x)((M_1/x)\cdot M_2)$. Set $N := L := M_1$; $M \to_{\beta\sigma}^{*} L$ is one `VarRef` step or `Comp$_\varepsilon$` then `VarRef`.

**`VarSkip`** ($x \neq y$). $⟦M⟧ = \varepsilon(x)((⟦M_1⟧/y)\cdot⟦M_2⟧)$, $N' = \varepsilon(x)\,⟦M_2⟧$, and $M = x \circ ((M_1/y)\cdot M_2)$ or $M = \varepsilon(x)((M_1/y)\cdot M_2)$. Set $N := L := x \circ M_2$. Then $⟦N⟧ = \varepsilon(x)\,⟦M_2⟧ = N'$; $M \to_{\beta\sigma}^{*} L$ is one `VarSkip` step or `Comp$_\varepsilon$` then `VarSkip`.

> The scanned source for this case renders $N'$ as "$x \circ ⟦M_2⟧$"; since $\lambda_{\mathrm{FREnv}}$ has no `Comp` constructor, that cannot be the literal target and is read here as $\varepsilon(x)\,⟦M_2⟧$, matching $\lambda_{\mathrm{FREnv}}$'s own `VarSkip` rule ($\varepsilon(y)((M/x)\cdot N) \to \varepsilon(y)N$) and keeping $⟦N⟧ = N'$ consistent.

**`DApp`.** $M$ is one of four shapes, according to whether each of the two represented sub-applications is written with `App` or with `Comp` in $\lambda_{\mathrm{Env}\varepsilon}$:

$$
\begin{array}{llll}
M = (M_1 M_2) \circ M_3, & ⟦M⟧ = \varepsilon(⟦M_1⟧\,⟦M_2⟧)\,⟦M_3⟧, & N' = (\varepsilon(⟦M_1⟧)⟦M_3⟧)(\varepsilon(⟦M_2⟧)⟦M_3⟧); \\
M = \varepsilon(M_1 M_2)\,M_3, & ⟦M⟧ = \varepsilon(⟦M_1⟧\,⟦M_2⟧)\,⟦M_3⟧, & N' = (\varepsilon(⟦M_1⟧)⟦M_3⟧)(\varepsilon(⟦M_2⟧)⟦M_3⟧); \\
M = (M_1 \circ M_2) \circ M_3, & ⟦M⟧ = \varepsilon(\varepsilon(⟦M_1⟧)⟦M_2⟧)\,⟦M_3⟧, & N' = (\varepsilon(\varepsilon(⟦M_1⟧))⟦M_3⟧)(\varepsilon(⟦M_2⟧)⟦M_3⟧); \\
M = \varepsilon(M_1 \circ M_2)\,M_3, & ⟦M⟧ = \varepsilon(\varepsilon(⟦M_1⟧)⟦M_2⟧)\,⟦M_3⟧, & N' = (\varepsilon(\varepsilon(⟦M_1⟧))⟦M_3⟧)(\varepsilon(⟦M_2⟧)⟦M_3⟧).
\end{array}
$$

If $M$ is one of the first two shapes, set $N := L := (M_1 \circ M_3)(M_2 \circ M_3)$: then $⟦N⟧ = N'$, and $M \to_{\beta\sigma}^{*} L$ is one `DApp` step (first shape) or `Comp$_\varepsilon$` then `DApp` (second shape).

If $M$ is one of the last two shapes, set $N := (\varepsilon(M_1) \circ M_3)(M_2 \circ M_3)$ and $L := M_1 \circ (M_2 \circ M_3)$. Then $⟦N⟧ = (\varepsilon(\varepsilon(⟦M_1⟧))⟦M_3⟧)(\varepsilon(⟦M_2⟧)⟦M_3⟧) = N'$. For $N \to_{\beta\sigma}^{*} L$: the left factor $\varepsilon(M_1) \circ M_3$ reduces via `Eps-eps` to $\varepsilon(M_1)$ (one step, lifted through `AppL`), giving $\varepsilon(M_1)(M_2 \circ M_3)$, which then reduces via `Comp$_\varepsilon$` to $M_1 \circ (M_2 \circ M_3) = L$ -- two steps total. For $M \to_{\beta\sigma}^{*} L$: the third shape reaches $L$ via one `Assoc` step; the fourth shape first fires `Comp$_\varepsilon$` to reach the third shape's term, then `Assoc`.

**`Eps-eps`.** $⟦M⟧ = \varepsilon(\varepsilon(⟦M_1⟧))\,⟦M_2⟧$, $N' = \varepsilon(⟦M_1⟧)$, and $M = \varepsilon(M_1) \circ M_2$ or $M = \varepsilon(\varepsilon(M_1))\,M_2$. Set $N := L := \varepsilon(M_1)$. Then $⟦N⟧ = N'$; $M \to_{\beta\sigma}^{*} L$ is one `Eps-eps` step (first shape) or `Comp$_\varepsilon$` then `Eps-eps` (second shape).

### Congruence rules

Each congruence rule case follows the same pattern: peel off the outer constructor, apply the induction hypothesis to the smaller derivation on the immediate subterm, and rebuild $N$ and $L$ by re-attaching the same outer constructor on the $\lambda_{\mathrm{Env}\varepsilon}$ side.

**`Lam`.** $M = \lambda x.\,M_1$, $⟦M⟧ = \lambda x.\,⟦M_1⟧$, and $⟦M_1⟧ \to_{\beta\sigma} N_1'$ with $N' = \lambda x.\,N_1'$, for some $\lambda_{\mathrm{Env}\varepsilon}$ term $M_1$ and $\lambda_{\mathrm{FREnv}}$ term $N_1'$. By the induction hypothesis (applied to $M_1$ and $N_1'$), there exist $\lambda_{\mathrm{Env}\varepsilon}$ terms $N_1, L_1$ with $⟦N_1⟧ = N_1'$, $N_1 \to_{\beta\sigma}^{*} L_1$, $M_1 \to_{\beta\sigma}^{*} L_1$. Set $N := \lambda x.\,N_1$, $L := \lambda x.\,L_1$. Then $⟦N⟧ = N'$, and both $N \to_{\beta\sigma}^{*} L$ and $M \to_{\beta\sigma}^{*} L$ follow by lifting $N_1 \to_{\beta\sigma}^{*} L_1$ and $M_1 \to_{\beta\sigma}^{*} L_1$ through the `Lam` congruence rule of $\lambda_{\mathrm{Env}\varepsilon}$.

**`Eop`.** $M = \varepsilon(M_1)$, $⟦M⟧ = \varepsilon(⟦M_1⟧)$, $⟦M_1⟧ \to_{\beta\sigma} N_1'$, $N' = \varepsilon(N_1')$. By the induction hypothesis, get $N_1, L_1$ with $⟦N_1⟧ = N_1'$, $N_1 \to_{\beta\sigma}^{*} L_1$, $M_1 \to_{\beta\sigma}^{*} L_1$. Set $N := \varepsilon(N_1)$, $L := \varepsilon(L_1)$; lift through `Eop`.

**`AppL`.** $M = M_1 M_2$, $⟦M⟧ = ⟦M_1⟧\,⟦M_2⟧$, $⟦M_1⟧ \to_{\beta\sigma} N_1'$, $N' = N_1'\,⟦M_2⟧$. By the induction hypothesis (applied to $M_1$, $N_1'$), get $N_1, L_1$ with $⟦N_1⟧ = N_1'$, $N_1 \to_{\beta\sigma}^{*} L_1$, $M_1 \to_{\beta\sigma}^{*} L_1$. Set $N := N_1\,M_2$, $L := L_1\,M_2$. Then $⟦N⟧ = ⟦N_1⟧\,⟦M_2⟧ = N'$, and both $N \to_{\beta\sigma}^{*} L$ and $M \to_{\beta\sigma}^{*} L$ follow by lifting through `AppL` (the right argument $M_2$ stays fixed throughout).

**`AppR`.** $M = M_1 M_2$, $⟦M⟧ = ⟦M_1⟧\,⟦M_2⟧$, $⟦M_2⟧ \to_{\beta\sigma} N_2'$, $N' = ⟦M_1⟧\,N_2'$. By the induction hypothesis (applied to $M_2$, $N_2'$), get $N_2, L_2$ with $⟦N_2⟧ = N_2'$, $N_2 \to_{\beta\sigma}^{*} L_2$, $M_2 \to_{\beta\sigma}^{*} L_2$. Set $N := M_1\,N_2$, $L := M_1\,L_2$; lift through `AppR` (the left argument $M_1$ stays fixed).

**`ExtnL`.** $M = (M_1/x)\cdot M_2$, $⟦M⟧ = (⟦M_1⟧/x)\cdot⟦M_2⟧$, $⟦M_1⟧ \to_{\beta\sigma} N_1'$, $N' = (N_1'/x)\cdot⟦M_2⟧$. By the induction hypothesis, get $N_1, L_1$ with $⟦N_1⟧ = N_1'$, $N_1 \to_{\beta\sigma}^{*} L_1$, $M_1 \to_{\beta\sigma}^{*} L_1$. Set $N := (N_1/x)\cdot M_2$, $L := (L_1/x)\cdot M_2$; lift through `ExtnL`.

**`ExtnR`.** $M = (M_1/x)\cdot M_2$, $⟦M⟧ = (⟦M_1⟧/x)\cdot⟦M_2⟧$, $⟦M_2⟧ \to_{\beta\sigma} N_2'$, $N' = (⟦M_1⟧/x)\cdot N_2'$. By the induction hypothesis, get $N_2, L_2$ with $⟦N_2⟧ = N_2'$, $N_2 \to_{\beta\sigma}^{*} L_2$, $M_2 \to_{\beta\sigma}^{*} L_2$. Set $N := (M_1/x)\cdot N_2$, $L := (M_1/x)\cdot L_2$; lift through `ExtnR`.

This exhausts every rule by which $⟦M⟧ \to_{\beta\sigma} N'$ could have been derived, so in every case there exist $\lambda_{\mathrm{Env}\varepsilon}$ terms $N, L$ with $⟦N⟧ = N'$, $N \to_{\beta\sigma}^{*} L$, and $M \to_{\beta\sigma}^{*} L$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **No confluence needed.** Every case above builds $N$ and $L$ *explicitly*, using only $\lambda_{\mathrm{Env}\varepsilon}$'s own reduction rules (`docs/enve-reduction-beta-sigma.md`) applied in a fixed, determined order. At no point are two independently-obtained reducts compared or joined after the fact -- so neither confluence nor local confluence of $\lambda_{\mathrm{FREnv}}$'s $\to_{\beta\sigma}$ (`docs/frenv-beta-sigma-local-confluence.md`) is used anywhere in this proof. The multiple $M$-shapes appearing in several cases (`Assoc`, `DApp`, and the `Comp$_\varepsilon$`-preceded variants throughout) exist because $⟦-⟧$ identifies `Comp M N` with `App (Eps M) N`, so a single $⟦M⟧$-shape can come from more than one $\lambda_{\mathrm{Env}\varepsilon}$ term; each such preimage is handled by its own short, explicit reduction to the same $L$, not by a joinability argument.
- **What this document replaces.** An earlier version of this file (then named `enve-frenv-translation-postponement.md`, stating a "Postponement Lemma") was written against an OCR transcription of the thesis that turned out to be unreliable for this section, leading to a different and, on closer analysis, only partially provable claim (needing local confluence for 15 of 19 cases and left genuinely open for the other 4, `AppL`/`AppR`/`CompL`/`CompR`). Having now been given a clear transcription of the actual proof, this document discards that reconstruction rather than trying to patch it, since the two claims are not equivalent.
- **One notational correction.** In the `VarSkip` case, the source renders the $\lambda_{\mathrm{FREnv}}$-side target as "$x \circ ⟦M_2⟧$", which cannot be literal since $\lambda_{\mathrm{FREnv}}$ has no `Comp` constructor (`docs/frenv-syntax.md`); it is read here as $\varepsilon(x)\,⟦M_2⟧$, the actual right-hand side of $\lambda_{\mathrm{FREnv}}$'s own `VarSkip` rule.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{FREnv}}$ and $\lambda_{\mathrm{Env}\varepsilon}$ have none (`docs/frenv-syntax.md`, `docs/enve-syntax.md`).
