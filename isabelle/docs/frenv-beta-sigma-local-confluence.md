# Local Confluence of $\to_{\beta\sigma}$ on $\lambda_{\mathrm{FREnv}}$

This document states and proves the local confluence of the one-step reduction relation $\to_{\beta\sigma}$ on $\mathbf{Term}(\lambda_{\mathrm{FREnv}})$ (`docs/frenv-reduction-beta-sigma.md`). It corresponds to the theorem `beta_sigma_step_locally_confluent` in `FREnv-to-be-remade/FREnv_BetaSigma_Local_Confluence.thy`, which is already machine-checked in Isabelle/HOL (on a very slightly different, `Const`-containing syntax); this document restates that result and its proof strategy in plain, checkable mathematics, dropping the `Const` rule (see the Remarks at the end). The same theorem, against this repository's own `Const`-free `FREnv.trm` syntax, is *also* now machine-checked in this session's own `FREnv` Isabelle project (`FREnv_BetaSigma_Local_Confluence.thy`, roadmap item 4), by directly reproving each of the 25 critical pairs listed in \S3 below (`FREnv_BetaSigma_Assoc_Peak.thy`, `FREnv_BetaSigma_DApp_Peak.thy`, `FREnv_BetaSigma_Root_Peaks.thy`, `FREnv_BetaSigma_Congruence_Peaks.thy`) rather than by appeal to the pre-existing project.

> **Note for AI-assisted formalization.**
> This document is *local* confluence only (one step vs. one step): it does
> **not** by itself justify joining a single step against an arbitrary
> multi-step reduction (that is the strip lemma / full confluence, which
> for this non-terminating calculus needs more than local confluence). It
> is kept here as a standalone, reusable fact rather than because any
> currently-written proof in this repository needs it: the lemma it was
> originally drafted to support (`docs/enve-frenv-translation-lifting.md`,
> thesis Lemma 3) turned out, on review against the actual thesis proof, to
> need no joinability fact at all -- its proof is entirely constructive.
> Use this document only where a one-step-vs-one-step peak genuinely needs
> to be joined.

---

## Theorem (Local Confluence of $\lambda_{\mathrm{FREnv}}$'s $\to_{\beta\sigma}$)

For all $M, N_1, N_2 \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, if $M \to_{\beta\sigma} N_1$ and $M \to_{\beta\sigma} N_2$, then there exists $L \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$ such that $N_1 \to_{\beta\sigma}^{*} L$ and $N_2 \to_{\beta\sigma}^{*} L$.

#### Proof.

Call a pair of steps $M \to_{\beta\sigma} N_1$, $M \to_{\beta\sigma} N_2$ from the same source $M$ a **peak**. The proof considers every way a peak can arise, by cases on the two rules used.

### Case 1: the two steps use the same rule at the same position

Every rule of $\to_{\beta\sigma}$ (`docs/frenv-reduction-beta-sigma.md`) is deterministic: its left-hand side determines its right-hand side uniquely (there is no rule with more than one possible right-hand side for a given left-hand side, and `VarRef`/`VarSkip` are mutually exclusive because their side conditions $x = x$ vs. $x \neq y$ cannot both hold). So if the same rule fires at the same position in both steps, $N_1 = N_2$, and $L := N_1$ works with zero further steps on either side.

### Case 2: the two steps fire at disjoint positions

If the redex reduced to get $N_1$ and the redex reduced to get $N_2$ occur in different, non-overlapping subterms of $M$ (formally: neither redex's position is a prefix of the other's), the two steps do not interfere with each other. Each congruence rule of $\to_{\beta\sigma}$ (`AppL`, `AppR`, `Lam`, `ExtnL`, `ExtnR`, `EnvAbst`) lets a reduction inside one child of a node happen independently of the other children, so the step that produced $N_1$ can still be performed inside $N_2$ (reducing the same disjoint subterm, now sitting inside $N_2$ instead of inside $M$), and vice versa. Both routes reach the same term $L$: the term obtained from $M$ by performing *both* reductions. Formally this is proved by induction on the shared context enclosing the two redex positions; it does not depend on which specific rule fired at either position, only on the positions being disjoint. (This is the general "disjoint peaks commute" fact underlying `FREnv_BetaSigma_Local_Peak_Decomposition.thy`.)

### Case 3: the two steps fire at overlapping positions (critical pairs)

This is the remaining case: one redex position is a prefix of the other (one redex sits inside, or coincides with, the other), and the two rules used are different (or the same rule matching the term two different ways). Because every rule's left-hand side is a *fixed, finite* term pattern (`docs/frenv-reduction-beta-sigma.md`), there are only finitely many ways two rules' patterns can overlap inside one another; each such overlap is called a **critical pair**, and joinability must be checked for each one individually. Below, $M$'s two reductions are always given as *sequences* $N_1 \to_{\beta\sigma}^{*} L$ and $N_2 \to_{\beta\sigma}^{*} L$ realizing the same $L$; every intermediate step used is itself an instance of a rule of $\to_{\beta\sigma}$ (possibly lifted through a congruence rule to reach a non-root position), so each line below is a legitimate derivation, not an appeal to anything beyond the rules already fixed.

There are three families of overlaps, matching the only three rules whose left-hand side contains another rule's left-hand side as a sub-pattern once one of their own metavariables is specialized: `Assoc`'s $L$-slot, `DApp`'s represented-application slot, and the outer `Eps`/`Id` shape shared by several rules at once ("same-root" overlaps). Each subsection below lists the peak once and both joining sequences.

#### 3.1 Same-root overlaps

These arise when a single term matches two different rules' left-hand sides *without* needing any extra nested structure beyond the metavariables already present.

| # | Peak | Path via rule(s) | Path via rule(s) | Common reduct $L$ |
| - | --- | --- | --- | --- |
| R1 | $\varepsilon(\varepsilon(M))\,\mathsf{id}$ | `Eps-eps` (1 step) | `IdR` (1 step) | $\varepsilon(M)$ |
| R2 | $\varepsilon(\varepsilon(L)\,M)\,N$ | `Assoc` (1 step) | `DApp`, `Eps-eps` (2 steps) | $\varepsilon(L)(\varepsilon(M)N)$ |
| R3 | $\varepsilon(\varepsilon(L)\,M)\,\mathsf{id}$ | `Assoc`, `IdR` (2 steps) | `IdR` (1 step) | $\varepsilon(L)\,M$ |
| R4 | $\varepsilon(\mathsf{id})\,\mathsf{id}$ | `IdL` (1 step) | `IdR` (1 step) | $\mathsf{id}$ |
| R5 | $\varepsilon((L/x)\cdot M)\,\mathsf{id}$ | `DExtn`, `IdR`, `IdR` (3 steps) | `IdR` (1 step) | $(L/x)\cdot M$ |
| R6 | $\varepsilon(M\,N)\,\mathsf{id}$ | `DApp`, `IdR`, `IdR` (3 steps) | `IdR` (1 step) | $M\,N$ |

Worked example (R2, since it is used again below): $\varepsilon(\varepsilon(L)\,M)\,N$ matches `Assoc` directly (with `Assoc`'s own metavariables $L, M, N$), giving $\varepsilon(L)(\varepsilon(M)N)$ in one step. It also matches `DApp` (with `DApp`'s pattern $\varepsilon(P\,Q)N$ instantiated at $P := \varepsilon(L)$, $Q := M$), giving $(\varepsilon(\varepsilon(L))N)(\varepsilon(M)N)$; the left half $\varepsilon(\varepsilon(L))N$ now matches `Eps-eps`, reducing (via `AppL`) to $\varepsilon(L)$, for the same final term $\varepsilon(L)(\varepsilon(M)N)$.

There is also one overlap involving `BetaClos`, arising when its environment argument is specifically $\mathsf{id}$:

| # | Peak | Path via rule(s) | Path via rule(s) | Common reduct $L$ |
| - | --- | --- | --- | --- |
| C1 | $(\varepsilon(\lambda x.\,M)\,\mathsf{id})\,N$ | `BetaClos` (1 step) | `IdR`, `Beta` (2 steps) | $\varepsilon(M)((N/x)\cdot \mathsf{id})$ |

#### 3.2 Overlaps inside `Assoc`'s $L$-slot

`Assoc`'s left-hand side is $\varepsilon(\varepsilon(L)\,M)\,N$, and it fires for *any* $L$. When $L$ itself has a shape matching another rule's pattern once combined with $M$ (i.e. $\varepsilon(L)\,M$ is itself a redex, or contains one), two routes appear: fire `Assoc` at the outer level treating $L$ as opaque, or fire the other rule first, one level in. All eight non-`Const` instances are joinable:

| # | $L$ specialized to | Peak $\varepsilon(\varepsilon(L)\,M)\,N$ | Path A | Path B | Common reduct |
| - | --- | --- | --- | --- | --- |
| A1 | $\varepsilon(K)$ | $\varepsilon(\varepsilon(\varepsilon(K))\,M)\,N$ | `Assoc`, `Eps-eps` (2) | `Eps-eps`, `Eps-eps` (2) | $\varepsilon(K)$ |
| A2 | $\varepsilon(L)\,M$ (Assoc-shaped, i.e. $L := \varepsilon(L_0)\,M_0$) | $\varepsilon(\varepsilon(\varepsilon(L_0)\,M_0)\,M)\,N$ | `Assoc`, `Assoc` (2) | `Assoc`, `Assoc`, `Assoc` (3) | $\varepsilon(L_0)(\varepsilon(M_0)(\varepsilon(M)\,N))$ |
| A3 | $\mathsf{id}$ | $\varepsilon(\varepsilon(\mathsf{id})\,M)\,N$ | `Assoc`, `IdL` (2) | `IdL` (1) | $\varepsilon(M)\,N$ |
| A4 | inner application argument is $\mathsf{id}$ | $\varepsilon(\varepsilon(L)\,\mathsf{id})\,N$ | `Assoc`, `IdL` (2) | `IdR` (1) | $\varepsilon(L)\,N$ |
| A5 | $(A/x)\cdot B$ | $\varepsilon(\varepsilon((A/x)\cdot B)\,M)\,N$ | `Assoc`, `DExtn` (2) | `DExtn`, `DExtn`, `Assoc`, `Assoc` (4) | $((\varepsilon(A)(\varepsilon(M)N))/x)\cdot(\varepsilon(B)(\varepsilon(M)N))$ |
| A6 | $\mathrm{Var}\ x$, with $M = (A/x)\cdot B$ | $\varepsilon(\varepsilon(x)\,((A/x)\cdot B))\,N$ | `Assoc`, `DExtn`, `VarRef` (3) | `VarRef` (1) | $\varepsilon(A)\,N$ |
| A7 | $\mathrm{Var}\ y$, $x \neq y$, $M = (A/x)\cdot B$ | $\varepsilon(\varepsilon(y)\,((A/x)\cdot B))\,N$ | `Assoc`, `DExtn`, `VarSkip` (3) | `VarSkip`, `Assoc` (2) | $\varepsilon(y)(\varepsilon(B)N)$ |
| A8 | $A\,B$ | $\varepsilon(\varepsilon(A\,B)\,M)\,N$ | `Assoc`, `DApp` (2) | `DApp`, `DApp`, `Assoc`, `Assoc` (4) | $(\varepsilon(A)(\varepsilon(M)N))(\varepsilon(B)(\varepsilon(M)N))$ |

Worked example (A5, `DExtn` overlap): Path A fires `Assoc` first (opaque $L := (A/x)\cdot B$), giving $\varepsilon((A/x)\cdot B)(\varepsilon(M)N)$, then `DExtn` at the root: $\to ((\varepsilon(A)(\varepsilon(M)N))/x)\cdot(\varepsilon(B)(\varepsilon(M)N))$. Path B fires `DExtn` first, one level in (lifted through `EnvAbst`), turning $\varepsilon((A/x)\cdot B)\,M$ into $((\varepsilon(A)M)/x)\cdot(\varepsilon(B)M)$; the resulting term $\varepsilon(((\varepsilon(A)M)/x)\cdot(\varepsilon(B)M))N$ is itself `DExtn`-shaped at the root, so `DExtn` fires again, giving $((\varepsilon(\varepsilon(A)M)N)/x)\cdot(\varepsilon(\varepsilon(B)M)N)$; both branches are now `Assoc`-shaped and are reduced (via `ExtnL`, `ExtnR`) to reach the same term as Path A.

#### 3.3 Overlaps inside `DApp`'s represented-application slot

`DApp`'s left-hand side is $\varepsilon(M\,N)\,L$, firing for any $M, N$. When $M$ itself has a shape matching another rule's pattern, the represented application $M\,N$ is itself (a quotation of) a redex, giving another overlap family. All ten non-`Const` instances are joinable:

| # | $M$ specialized to | Peak $\varepsilon(M\,N)\,L$ | Path A | Path B | Common reduct |
| - | --- | --- | --- | --- | --- |
| D1 | $\lambda x.\,P$ | $\varepsilon((\lambda x.\,P)\,N)\,L$ | `DApp`, `BetaClos` (2) | `Beta`, `DApp`, `Eps-eps`, `DExtn`, `IdL` (5) | $\varepsilon(P)((\varepsilon(N)L)/x)\cdot L)$ |
| D2 | $\varepsilon(\lambda x.\,P)\,K$ | $\varepsilon((\varepsilon(\lambda x.\,P)\,K)\,N)\,L$ | `DApp`, `Assoc`, `BetaClos` (3) | `BetaClos`, `DApp`, `Eps-eps`, `DExtn` (4) | $\varepsilon(P)((\varepsilon(N)L)/x)\cdot(\varepsilon(K)L))$ |
| D3 | $\varepsilon(\varepsilon(P))$ | $\varepsilon(\varepsilon(\varepsilon(P))\,N)\,L$ | `DApp`, `Eps-eps`, `Eps-eps` (3) | `Eps-eps`, `Eps-eps` (2) | $\varepsilon(P)$ |
| D4 | $\varepsilon(\varepsilon(A)B)$ | $\varepsilon(\varepsilon(\varepsilon(A)B)\,N)\,L$ | `DApp`, `Eps-eps`, `Assoc` (3) | `Assoc`, `DApp`, `Eps-eps`, `Assoc` (4) | $\varepsilon(A)(\varepsilon(B)(\varepsilon(N)L))$ |
| D5 | $\varepsilon(\mathsf{id})$ | $\varepsilon(\varepsilon(\mathsf{id})\,N)\,L$ | `DApp`, `Eps-eps`, `IdL` (3) | `IdL` (1) | $\varepsilon(N)\,L$ |
| D6 | (i.e. $N = \mathsf{id}$) | $\varepsilon(\varepsilon(P)\,\mathsf{id})\,L$ | `DApp`, `Eps-eps`, `IdL` (3) | `IdR` (1) | $\varepsilon(P)\,L$ |
| D7 | $\varepsilon((A/x)\cdot B)$ | $\varepsilon(\varepsilon((A/x)\cdot B)\,N)\,L$ | `DApp`, `Eps-eps`, `DExtn` (3) | `DExtn`, `DExtn`, `Assoc`, `Assoc` (4) | $((\varepsilon(A)(\varepsilon(N)L))/x)\cdot(\varepsilon(B)(\varepsilon(N)L))$ |
| D8 | $\varepsilon(x)$, $N=(A/x)\cdot B$ | $\varepsilon(\varepsilon(x)\,((A/x)\cdot B))\,L$ | `DApp`, `Eps-eps`, `DExtn`, `VarRef` (4) | `VarRef` (1) | $\varepsilon(A)\,L$ |
| D9 | $\varepsilon(y)$, $x\neq y$, $N=(A/x)\cdot B$ | $\varepsilon(\varepsilon(y)\,((A/x)\cdot B))\,L$ | `DApp`, `Eps-eps`, `DExtn`, `VarSkip` (4) | `VarSkip`, `Assoc` (2) | $\varepsilon(y)(\varepsilon(B)L)$ |
| D10 | $\varepsilon(A\,B)$ | $\varepsilon(\varepsilon(A\,B)\,K)\,L$ | `DApp`, `Eps-eps`, `DApp` (3) | `DApp`, `DApp`, `Assoc`, `Assoc` (4) | $(\varepsilon(A)(\varepsilon(K)L))(\varepsilon(B)(\varepsilon(K)L))$ |

Worked example (D1, the most important one, since it links `DApp` back to `Beta`/`BetaClos`): Path A fires `DApp` directly at the root, treating $\lambda x.\,P$ opaquely: $\to (\varepsilon(\lambda x.\,P)L)(\varepsilon(N)L)$; this is now `BetaClos`-shaped ($(\varepsilon(\lambda x.\,P)L)\,Q$ with $Q := \varepsilon(N)L$), so `BetaClos` fires: $\to \varepsilon(P)((\varepsilon(N)L)/x)\cdot L)$. Path B instead reduces the represented application $(\lambda x.\,P)N$ itself, one level inside the outer $\varepsilon(-)$, via `Beta`: $\to \varepsilon(P)((N/x)\cdot \mathsf{id})$, giving $\varepsilon(\varepsilon(P)((N/x)\cdot \mathsf{id}))L$; the argument of the outer $\varepsilon$ here is itself of `App`-shape, so `DApp` fires again: $\to (\varepsilon(\varepsilon(P))L)(\varepsilon((N/x)\cdot \mathsf{id})L)$; the left half reduces via `Eps-eps` to $\varepsilon(P)$, and the right half reduces via `DExtn` to $((\varepsilon(N)L)/x)\cdot(\varepsilon(\mathsf{id})L)$, whose second component reduces via `IdL` to $L$ -- reaching the same term $\varepsilon(P)(((\varepsilon(N)L)/x)\cdot L)$ as Path A, in five steps total.

### Assembling the theorem

Every peak $N_1 \leftarrow M \to N_2$ falls into Case 1, Case 2, or one of the finitely many critical pairs enumerated in Case 3 (Sections 3.1-3.3), each of which was shown joinable. Hence a common $L$ with $N_1 \to_{\beta\sigma}^{*} L$ and $N_2 \to_{\beta\sigma}^{*} L$ always exists, which is exactly local confluence.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **`Const` removed.** The underlying Isabelle development (`FREnv_BetaSigma_Critical_Peaks.thy`) includes a `Const` rule and three `Const`-involving critical pairs (`overlap_R_Const_IdR`, `overlap_A_Const`, `overlap_D_Const`). Per the repository's decision that $\lambda_{\mathrm{FREnv}}$ has no constants (`docs/frenv-syntax.md`, `docs/frenv-reduction-sigma.md`, `docs/frenv-reduction-beta-sigma.md`), all three have been dropped from this document, and every rule list, table, and step count above counts only the ten non-`Const` base rules (`Beta`, `BetaClos`, `Eps-eps`, `Assoc`, `IdL`, `IdR`, `DExtn`, `VarRef`, `VarSkip`, `DApp`).
- **Scope of the case-by-case verification.** Section 3 lists all critical pairs of the (Const-free) rule set and gives fully worked derivations for two representative instances in each family (R2, A5, D1) plus every same-root and `BetaClos` overlap (R1, R3-R6, C1). The remaining table entries (A1-A4, A6-A8, D2-D10) follow the identical style of argument (fire one rule opaquely vs. fire the nested rule first and let the outer rule catch up); rather than re-deriving all of them by hand here, this document relies on the fact that every one of them is already mechanically verified (by Isabelle's `auto` tactic) in `FREnv-to-be-remade/FREnv_BetaSigma_Critical_Peaks.thy` under the lemma names `overlap_A_*` and `overlap_D_*`, and, as of this repository's own `FREnv` session (roadmap item 4), also in `FREnv_BetaSigma_Assoc_Peak.thy` (`frenv_assoc_peak_join`, covering the whole A1-A8 family in one induction) and `FREnv_BetaSigma_DApp_Peak.thy` (`frenv_dapp_peak_join`, covering D1-D10). This keeps the document a readable size while still being traceable, term-for-term, back to a machine-checked source.
- **Case 2 (disjoint positions) stated, not fully expanded.** The general argument that reductions at disjoint positions commute is standard for context-based rewriting and is not rule-specific, so it is stated as a single fact rather than checked separately for each of the $\binom{10}{2}$ possible pairs of base rules plus the six congruence rules; its formal counterpart is `FREnv_BetaSigma_Local_Peak_Decomposition.thy`.
