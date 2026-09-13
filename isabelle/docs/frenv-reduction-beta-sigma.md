# Reduction of $\lambda_{\mathrm{FREnv}}$


# Definition (Reduction $\to_{\beta\sigma}$)

The one-step reduction relation $\to_{\beta\sigma}$ on $\mathbf{Term}$ is the least relation satisfying all computation rules and compatibility rules below.

### Beta rules:

#### Beta:
$$
((\lambda x. M)N)
\to_{\beta\sigma}
(\varepsilon(M)((N/x)\cdot \mathsf{id})).
$$

#### BetaClos:
$$
((\varepsilon(\lambda x. M) L) N)
\to_{\beta\sigma}
(\varepsilon(M)((N/x)\cdot L)).
$$

### Non-beta rules:

#### Assoc:
$$
\varepsilon((\varepsilon(L) M)) N
\to_{\beta\sigma}
\varepsilon(L)(\varepsilon(M) N).
$$

#### IdL:
$$
(\varepsilon(\mathsf{id})M)
\to_{\beta\sigma}
M.
$$

#### IdR:
$$
(\varepsilon(M)\mathsf{id})
\to_{\beta\sigma}
M.
$$

#### DExtn:
$$
(\varepsilon((L/x)\cdot M)N)
\to_{\beta\sigma}
((\varepsilon(L)N)/x)\cdot(\varepsilon(M)N).
$$

#### VarRef:
$$
(\varepsilon(x)((M/x)\cdot N))
\to_{\beta\sigma}
M.
$$

#### VarSkip:
$$
\begin{prooftree}
\AxiomC{$x \neq y$}
\UnaryInfC{$(\varepsilon(y)((M/x)\cdot N)) \to_{\beta\sigma} (\varepsilon(y)N)$}
\end{prooftree}
$$
(If $x \neq y$, then $\varepsilon(y)((M/x) \cdot N)$ reduces to $\varepsilon(y)N$.)

#### DApp:
$$
(\varepsilon((MN))L)
\to_{\beta\sigma}
((\varepsilon(M)L)(\varepsilon(N)L)).
$$

#### Eps-eps:
$$
(\varepsilon(\varepsilon(M))N)
\to_{\beta\sigma}
\varepsilon(M).
$$
(An already environment-abstracted term $\varepsilon(M)$ remains stable
under a further environment reference: $\varepsilon(\varepsilon(M))N$
reduces directly to $\varepsilon(M)$.)

### Compatibility Rules:

#### AppL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} N$}
\RightLabel{AppL}
\UnaryInfC{$(M L) \to_{\beta\sigma} (N L)$}
\end{prooftree}
$$
(If $M \to_{\beta\sigma} N$, then $(M L) \to_{\beta\sigma} (N L)$.)

#### AppR:
$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} N$}
\RightLabel{AppR}
\UnaryInfC{$(L M) \to_{\beta\sigma} (L N)$}
\end{prooftree}
$$
(If $M \to_{\beta\sigma} N$, we may infer $(L M) \to_{\beta\sigma} (L N)$.)


#### Lam:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{Lam}
\UnaryInfC{$\lambda x. M \to_{\beta\sigma} \lambda x. M'$}
\end{prooftree}
$$
(If $M \to_{\beta\sigma} M'$, then $\lambda x. M \to_{\beta\sigma} \lambda x. M'$.)

#### ExtnL:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} N$}
\RightLabel{ExtnL}
\UnaryInfC{$(M/x) \cdot L \to_{\beta\sigma} (N/x) \cdot L$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} N$, then $(M/x)\cdot L \to_{\beta\sigma} (N/x)\cdot L$.)

#### ExtnR:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} N$}
\RightLabel{ExtnR}
\UnaryInfC{$(L/x) \cdot M \to_{\beta\sigma} (L/x) \cdot N$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} N$, then $(L/x)\cdot M \to_{\beta\sigma} (L/x)\cdot N$.)

#### EnvAbst:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{EnvAbst}
\UnaryInfC{$\varepsilon(M) \to_{\beta\sigma} \varepsilon(M')$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} M'$, then $\varepsilon(M) \to_{\beta\sigma} \varepsilon(M')$.)


#### Definition (Relation $\to_{\beta\sigma}^*$)

The reflexive and transitive closure of $\to_{\beta\sigma}$ is written as $\to_{\beta\sigma}^{*}$.

Thus, $M \to_{\beta\sigma}^{*} N$ means that $M$ reduces to $N$ in zero or more steps.

## Informal Reading

The rules can be understood as describing how ordinary lambda-calculus computation is simulated by explicit environments.

A beta reduction does not immediately substitute the argument into the body. Instead, it constructs an environment that records the binding of the formal parameter to the argument. The term $\varepsilon(M)$ is then used to interpret the body $M$ under this environment.

Variable lookup is performed by traversing environment extensions. If the variable at the head of the environment is the one being referenced, the corresponding term is returned. If it is different, the rule skips that binding and continues with the remaining environment.

The identity environment acts as a neutral element. Interpreting a term under the identity environment leaves it unchanged, and interpreting the identity environment under another environment yields that environment.

The distribution rules explain how environment reference propagates through the structure of terms. In particular, it distributes over application and environment extension, while an already environment-abstracted term remains stable under further environment reference.
