# Termination of $\sigma$-Reduction on $\lambda_{\mathrm{Env}\varepsilon}$

This document states and proves thesis Theorem 4 (§2.3.1): the $\sigma$-reduction relation $\to_{\sigma}$ on $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-reduction-sigma.md`) is terminating -- there is no infinite $\to_{\sigma}$-reduction sequence. The thesis proof is a one-line corollary of Theorem 3; this document spells out why that one line is enough.

> **Note for AI-assisted formalization.**
> This is the standard "termination from a well-founded decreasing measure"
> argument. The measure is `length` (`docs/enve-term-length-measure.md`,
> thesis Definition 11), and the fact that it strictly decreases along
> every $\to_{\sigma}$-step is the Length Decrease Lemma
> (`docs/enve-sigma-reduction-length-decrease.md`, thesis Theorem 3). No
> new machinery is introduced here beyond combining those two facts with
> the ordinary well-ordering of the positive integers.

---

## Theorem (Termination of $\sigma$-Reduction)

There is no infinite sequence of $\lambda_{\mathrm{Env}\varepsilon}$ terms $M_0, M_1, M_2, \ldots$ such that $M_0 \to_{\sigma} M_1 \to_{\sigma} M_2 \to_{\sigma} \cdots$ (i.e. $\to_{\sigma}$ is terminating, equivalently strongly normalizing).

#### Proof.

Suppose, for contradiction, that such an infinite sequence $M_0 \to_{\sigma} M_1 \to_{\sigma} M_2 \to_{\sigma} \cdots$ exists.

By the Length Decrease Lemma (`docs/enve-sigma-reduction-length-decrease.md`, thesis Theorem 3), $M_i \to_{\sigma} M_{i+1}$ implies $\mathrm{length}(M_i) > \mathrm{length}(M_{i+1})$ for every $i \geq 0$. Applying this to every step of the sequence gives an infinite strictly decreasing sequence of integers
$$
\mathrm{length}(M_0) > \mathrm{length}(M_1) > \mathrm{length}(M_2) > \cdots.
$$

By Definition 11 (`docs/enve-term-length-measure.md`), `length` takes values in the positive integers, so every term in this sequence satisfies $\mathrm{length}(M_i) \geq 1$. But the positive integers (indeed, all natural numbers) are well-ordered: there is no infinite strictly decreasing sequence of positive integers, since after at most $\mathrm{length}(M_0) - 1$ steps the sequence would have to drop below $1$, which is impossible. This is a contradiction.

Hence no such infinite sequence $M_0 \to_{\sigma} M_1 \to_{\sigma} M_2 \to_{\sigma} \cdots$ exists, i.e. $\to_{\sigma}$ is terminating.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Expanded from the source's one-line proof.** The thesis states this theorem's proof as "follows from Theorem 3" without further elaboration. This document spells out the standard argument that licenses that one line: a strictly-decreasing, positive-integer-valued measure along every reduction step rules out infinite reduction sequences, by the well-ordering of the positive integers. No additional facts beyond the Length Decrease Lemma and this well-ordering principle are used.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
