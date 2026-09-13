# Reduction of $\lambda_{\mathrm{FREnv}}$


# Definition (Sub-reduction $\to_{\sigma}$)

The one-step reduction relation $\to_{\sigma}$ on $\mathbf{Term}$ is the least relation satisfying all computation rules and compatibility rules below.

### Non-beta rules:

#### Assoc:
$$
\varepsilon((\varepsilon(L) M)) N
\to_{\sigma}
\varepsilon(L)(\varepsilon(M) N).
$$

#### IdL:
$$
(\varepsilon(\mathsf{id})M)
\to_{\sigma}
M.
$$

#### IdR:
$$
(\varepsilon(M)\mathsf{id})
\to_{\sigma}
M.
$$

#### DExtn:
$$
(\varepsilon((L/x)\cdot M)N)
\to_{\sigma}
((\varepsilon(L)N)/x)\cdot(\varepsilon(M)N).
$$

#### VarRef:
$$
(\varepsilon(x)((M/x)\cdot N))
\to_{\sigma}
M.
$$

#### VarSkip:
$$
\begin{prooftree}
\AxiomC{$x \neq y$}
\UnaryInfC{$(\varepsilon(y)((M/x)\cdot N)) \to_{\sigma} (\varepsilon(y)N)$}
\end{prooftree}
$$
(If $x \neq y$, then $\varepsilon(y)((M/x) \cdot N)$ reduces to $\varepsilon(y)N$.)

#### DApp:
$$
(\varepsilon((MN))L)
\to_{\sigma}
((\varepsilon(M)L)(\varepsilon(N)L)).
$$

#### Const:
$$
\varepsilon(c)M \to_{\sigma} c.
$$

### Compatibility Rules:

#### AppL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} N$}
\RightLabel{AppL}
\UnaryInfC{$(M L) \to_{\sigma} (N L)$}
\end{prooftree}
$$
(If $M \to_{\sigma} N$, then $(M L) \to_{\sigma} (N L)$.)

#### AppR:
$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} N$}
\RightLabel{AppR}
\UnaryInfC{$(L M) \to_{\sigma} (L N)$}
\end{prooftree}
$$
(If $M \to_{\sigma} N$, we may infer $(L M) \to_{\sigma} (L N)$.)


#### Lam:

$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{Lam}
\UnaryInfC{$\lambda x. M \to_{\sigma} \lambda x. M'$}
\end{prooftree}
$$
(If $M \to_{\sigma} M'$, then $\lambda x. M \to_{\sigma} \lambda x. M'$.)

#### ExtnL:

$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} N$}
\RightLabel{ExtnL}
\UnaryInfC{$(M/x) \cdot L \to_{\sigma} (N/x) \cdot L$}
\end{prooftree}
$$

(If $M \to_{\sigma} N$, then $(M/x)\cdot L \to_{\sigma} (N/x)\cdot L$.)

#### ExtnR:

$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} N$}
\RightLabel{ExtnR}
\UnaryInfC{$(L/x) \cdot M \to_{\sigma} (L/x) \cdot N$}
\end{prooftree}
$$

(If $M \to_{\sigma} N$, then $(L/x)\cdot M \to_{\sigma} (L/x)\cdot N$.)

#### EnvAbst:

$$
\begin{prooftree}
\AxiomC{$M \to_{\sigma} M'$}
\RightLabel{EnvAbst}
\UnaryInfC{$\varepsilon(M) \to_{\sigma} \varepsilon(M')$}
\end{prooftree}
$$

(If $M \to_{\sigma} M'$, then $\varepsilon(M) \to_{\sigma} \varepsilon(M')$.)


#### Definition (Relation $\to_{\sigma}^*$)

The reflexive and transitive closure of $\to_{\sigma}$ is written as $\to_{\sigma}^{*}$.

Thus, $M \to_{\sigma}^{*} N$ means that $M$ reduces to $N$ in zero or more steps.

