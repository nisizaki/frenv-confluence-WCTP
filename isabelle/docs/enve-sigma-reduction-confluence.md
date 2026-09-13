# Confluence of $\sigma$-Reduction on $\lambda_{\mathrm{Env}\varepsilon}$

This document states and proves thesis Theorem 5 (§2.4.2): the $\sigma$-reduction relation $\to_{\sigma}$ on $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-reduction-sigma.md`) is confluent (satisfies the Church-Rosser property). The thesis proof is one line -- "follows from Theorem 4, Lemma 5, and Newman's Lemma" -- combining two facts already established in this repository with a classical, standard result from rewriting theory. This document spells that combination out.

> **Note for AI-assisted formalization.**
> The two ingredients this theorem combines are already proved elsewhere
> in this repository: termination of $\to_{\sigma}$
> (`docs/enve-sigma-reduction-termination.md`, thesis Theorem 4) and local
> confluence of $\to_{\sigma}$
> (`docs/enve-sigma-reduction-local-confluence.md`, thesis Lemma 5). The
> only new ingredient here is Newman's Lemma itself, a well-known general
> fact about abstract rewriting systems (not specific to
> $\lambda_{\mathrm{Env}\varepsilon}$); it is stated below and cited rather
> than re-proved from scratch, since it is standard textbook material
> (Newman, 1942) with no dependency on the details of this calculus.

---

## Theorem (Confluence of $\sigma$-Reduction)

For all $M, N_1, N_2 \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\sigma}^{*} N_1$ and $M \to_{\sigma}^{*} N_2$, then there exists $L \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ such that $N_1 \to_{\sigma}^{*} L$ and $N_2 \to_{\sigma}^{*} L$.

#### Proof.

The proof combines three facts.

**Fact 1 (Termination, thesis Theorem 4).** $\to_{\sigma}$ has no infinite reduction sequence (`docs/enve-sigma-reduction-termination.md`).

**Fact 2 (Local confluence, thesis Lemma 5).** For all $P, Q_1, Q_2$, if $P \to_{\sigma} Q_1$ and $P \to_{\sigma} Q_2$, there is $R$ with $Q_1 \to_{\sigma}^{*} R$ and $Q_2 \to_{\sigma}^{*} R$ (`docs/enve-sigma-reduction-local-confluence.md`).

**Fact 3 (Newman's Lemma).** For *any* binary relation $\to$ on *any* set: if $\to$ is terminating and locally confluent, then $\to$ is confluent.

Facts 1 and 2 say exactly that $\to_{\sigma}$ satisfies the two hypotheses of Newman's Lemma. Applying Fact 3 with $\to := \to_{\sigma}$ then gives precisely the conclusion of this theorem: confluence of $\to_{\sigma}$.

It remains to justify Fact 3, since (unlike Facts 1 and 2) it is not specific to $\lambda_{\mathrm{Env}\varepsilon}$ and has not been proved elsewhere in this repository. The standard argument is well-founded induction on $M$ with respect to $\to$ (which is available precisely because $\to$ is terminating, by Fact 1's hypothesis): suppose $M \to^{*} N_1$ and $M \to^{*} N_2$.

- If $M = N_1$ or $M = N_2$, take $L$ to be the other one; it is trivially reached from itself in zero steps and from $M$ by the given sequence.
- Otherwise, write the two reduction sequences as $M \to M_1 \to^{*} N_1$ and $M \to M_2 \to^{*} N_2$ for some first steps $M \to M_1$ and $M \to M_2$ (possibly with $M_1 = M_2$, in which case the two sequences already share a starting point one step in, and the induction hypothesis applied to $M_1$ finishes the case immediately). If $M_1 \neq M_2$: by local confluence (Fact 2) applied to the peak $M_1 \leftarrow M \to M_2$, there is $P$ with $M_1 \to^{*} P$ and $M_2 \to^{*} P$. Since $M \to M_1$ is a step of $\to$, the induction hypothesis applies to $M_1$ (it is "smaller" than $M$ in the well-founded order given by termination), so from $M_1 \to^{*} N_1$ and $M_1 \to^{*} P$ we get a common reduct $Q_1$ with $N_1 \to^{*} Q_1$ and $P \to^{*} Q_1$. Likewise, applying the induction hypothesis to $M_2$ with its two reductions $M_2 \to^{*} N_2$ and $M_2 \to^{*} P$ gives a common reduct $Q_2$ with $N_2 \to^{*} Q_2$ and $P \to^{*} Q_2$. Finally, $P \to^{*} Q_1$ and $P \to^{*} Q_2$ are two reductions from $P$, and $P$ is again "smaller" than $M$ (it is reached from $M_1$, which is smaller than $M$), so the induction hypothesis applies once more to $P$, giving $L$ with $Q_1 \to^{*} L$ and $Q_2 \to^{*} L$. Chaining, $N_1 \to^{*} Q_1 \to^{*} L$ and $N_2 \to^{*} Q_2 \to^{*} L$, which is the required common reduct for $M$.

This completes Fact 3, and with it the theorem: $\to_{\sigma}$ is confluent.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Expanded from the source's one-line proof.** The thesis states this theorem's proof as "follows from Theorem 4, Lemma 5, and Newman's Lemma" without stating Newman's Lemma itself or justifying it. This document states it precisely (Fact 3) and includes its standard proof (well-founded induction on the terminating relation, using local confluence at each step), since Newman's Lemma is exactly the piece of the argument that is not otherwise recorded anywhere in this repository.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
