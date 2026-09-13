# Reduction of $\lambda_{\mathrm{Env}\varepsilon}$ (Sub-reduction)


# Definition (Sub-reduction $\to_{\sigma}$)

The one-step reduction relation $\to_{\sigma}$ on $\mathbf{Term}$ is the least relation satisfying all substitution rules (thesis Definition 6) and congruence rules (thesis Definition 7) below.

> **Note.**  Unlike $\lambda_{\mathrm{FREnv}}$, the substitution rules of
> $\lambda_{\mathrm{Env}\varepsilon}$ are stated in terms of the primitive
> environment-composition constructor `Comp M N` ($M \circ N$), not directly
> on applications of the form $\varepsilon(M)N$.  The rule that turns such an
> application into a composition, $\varepsilon(M)N \to M \circ N$
> ($\mathrm{Comp}_{\varepsilon}$, thesis Definition 5), belongs to the
> **Beta rule** together with `Beta` and `BetaClos`, and is therefore *not*
> part of $\to_{\sigma}$ -- it is documented separately, alongside `Beta` and
> `BetaClos`, once the beta-reduction relation is written up.  All of the
> rules below act on `Comp M N` once it has already appeared as a subterm.

### Substitution rules (thesis Definition 6):

#### Assoc:
$$
(M \circ N) \circ L
\to_{\sigma}
M \circ (N \circ L).
$$

#### IdL:
$$
\mathsf{id} \circ M
\to_{\sigma}
M.
$$

#### IdR:
$$
M \circ \mathsf{id}
\to_{\sigma}
M.
$$

#### DExtn:
$$
((L/x)\cdot M) \circ N
\to_{\sigma}
((L \circ N)/x)\cdot(M \circ N).
$$

#### VarRef:
$$
x \circ ((M/x)\cdot N)
\to_{\sigma}
M.
$$

#### VarSkip:
$$
\begin{prooftree}
\AxiomC{$x \neq y$}
\UnaryInfC{$x \circ ((M/y)\cdot N) \to_{\sigma} x \circ N$}
\end{prooftree}
$$
(If $x \neq y$, then $x \circ ((M/y) \cdot N)$ reduces to $x \circ N$.)

#### DApp:
$$
(M\,N) \circ L
\to_{\sigma}
(M \circ L)\,(N \circ L).
$$

#### Eps-eps:
$$
\varepsilon(M) \circ N
\to_{\sigma}
\varepsilon(M).
$$
(Composing an environment-abstraction term $\varepsilon(M)$ with any further
environment $N$ leaves $\varepsilon(M)$ unchanged: once a term is headed by
`Eps`, it no longer depends on the environment it is composed with. This is
the $\lambda_{\mathrm{Env}\varepsilon}$ counterpart of the `Eps-eps` rule of
$\lambda_{\mathrm{FREnv}}$, restated for `Comp` instead of `App`.)

### Congruence Rules (thesis Definition 7):

#### AppL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{AppL}
\UnaryInfC{$M\,N \to_{\sigma} M'\,N$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $M\,N \to_{\sigma} M'\,N$.)

#### AppR:
$$
\begin{prooftree}
\AxiomC{$N \to_{\sigma} N'$}
\RightLabel{AppR}
\UnaryInfC{$M\,N \to_{\sigma} M\,N'$}
\end{prooftree}
$$
(If $N \to_{\sigma} N'$, then $M\,N \to_{\sigma} M\,N'$.)

#### Lam:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{Lam}
\UnaryInfC{$\lambda x.\,M \to_{\sigma} \lambda x.\,M'$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $\lambda x.\,M \to_{\sigma} \lambda x.\,M'$.)

#### ExtnL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{ExtnL}
\UnaryInfC{$(M/x) \cdot N \to_{\sigma} (M'/x) \cdot N$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $(M/x)\cdot N \to_{\sigma} (M'/x)\cdot N$.)

#### ExtnR:
$$
\begin{prooftree}
\AxiomC{$N \to_{\sigma} N'$}
\RightLabel{ExtnR}
\UnaryInfC{$(M/x) \cdot N \to_{\sigma} (M/x) \cdot N'$}
\end{prooftree}
$$
(If $N \to_{\sigma} N'$, then $(M/x)\cdot N \to_{\sigma} (M/x)\cdot N'$.)

#### CompL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{CompL}
\UnaryInfC{$M \circ N \to_{\sigma} M' \circ N$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $M \circ N \to_{\sigma} M' \circ N$.)

#### CompR:
$$
\begin{prooftree}
\AxiomC{$N \to_{\sigma} N'$}
\RightLabel{CompR}
\UnaryInfC{$M \circ N \to_{\sigma} M \circ N'$}
\end{prooftree}
$$
(If $N \to_{\sigma} N'$, then $M \circ N \to_{\sigma} M \circ N'$.)

#### Eop:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{Eop}
\UnaryInfC{$\varepsilon(M) \to_{\sigma} \varepsilon(M')$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $\varepsilon(M) \to_{\sigma} \varepsilon(M')$.
This is the $\lambda_{\mathrm{Env}\varepsilon}$ congruence rule for `Eps`,
corresponding to `EnvAbst` in $\lambda_{\mathrm{FREnv}}$.)


#### Definition (Relation $\to_{\sigma}^*$)

The reflexive and transitive closure of $\to_{\sigma}$ is written as $\to_{\sigma}^{*}$.

Thus, $M \to_{\sigma}^{*} N$ means that $M$ reduces to $N$ in zero or more steps.
