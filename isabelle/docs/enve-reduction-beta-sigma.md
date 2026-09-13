# Reduction of $\lambda_{\mathrm{Env}\varepsilon}$


# Definition (Reduction $\to_{\beta\sigma}$)

The one-step reduction relation $\to_{\beta\sigma}$ on $\mathbf{Term}$ is the least relation satisfying all beta rules (thesis Definition 5), substitution rules (thesis Definition 6), and congruence rules (thesis Definition 7) below.

### Beta rules:

#### Beta:
$$
((\lambda x. M)N)
\to_{\beta\sigma}
(M \circ ((N/x)\cdot \mathsf{id})).
$$

#### BetaClos:
$$
(((\lambda x. M) \circ L) N)
\to_{\beta\sigma}
(M \circ ((N/x)\cdot L)).
$$

#### Comp (Comp$_{\varepsilon}$):
$$
(\varepsilon(M)N)
\to_{\beta\sigma}
M \circ N.
$$

### Substitution rules:

#### Assoc:
$$
(M \circ N) \circ L
\to_{\beta\sigma}
M \circ (N \circ L).
$$

#### IdL:
$$
\mathsf{id} \circ M
\to_{\beta\sigma}
M.
$$

#### IdR:
$$
M \circ \mathsf{id}
\to_{\beta\sigma}
M.
$$

#### DExtn:
$$
((L/x)\cdot M) \circ N
\to_{\beta\sigma}
((L \circ N)/x)\cdot(M \circ N).
$$

#### VarRef:
$$
x \circ ((M/x)\cdot N)
\to_{\beta\sigma}
M.
$$

#### VarSkip:
$$
\begin{prooftree}
\AxiomC{$x \neq y$}
\UnaryInfC{$x \circ ((M/y)\cdot N) \to_{\beta\sigma} x \circ N$}
\end{prooftree}
$$
(If $x \neq y$, then $x \circ ((M/y) \cdot N)$ reduces to $x \circ N$.)

#### DApp:
$$
(M\,N) \circ L
\to_{\beta\sigma}
(M \circ L)\,(N \circ L).
$$

#### Eps-eps:
$$
\varepsilon(M) \circ N
\to_{\beta\sigma}
\varepsilon(M).
$$

### Compatibility Rules:

#### AppL:
$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{AppL}
\UnaryInfC{$M\,N \to_{\beta\sigma} M'\,N$}
\end{prooftree}
$$
(If $M \to_{\beta\sigma} M'$, then $M\,N \to_{\beta\sigma} M'\,N$.)

#### AppR:
$$
\begin{prooftree}
\AxiomC{$N \to_{\beta\sigma} N'$}
\RightLabel{AppR}
\UnaryInfC{$M\,N \to_{\beta\sigma} M\,N'$}
\end{prooftree}
$$
(If $N \to_{\beta\sigma} N'$, then $M\,N \to_{\beta\sigma} M\,N'$.)

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
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{ExtnL}
\UnaryInfC{$(M/x) \cdot N \to_{\beta\sigma} (M'/x) \cdot N$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} M'$, then $(M/x)\cdot N \to_{\beta\sigma} (M'/x)\cdot N$.)

#### ExtnR:

$$
\begin{prooftree}
\AxiomC{$N \to_{\beta\sigma} N'$}
\RightLabel{ExtnR}
\UnaryInfC{$(M/x) \cdot N \to_{\beta\sigma} (M/x) \cdot N'$}
\end{prooftree}
$$

(If $N \to_{\beta\sigma} N'$, then $(M/x)\cdot N \to_{\beta\sigma} (M/x)\cdot N'$.)

#### CompL:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{CompL}
\UnaryInfC{$M \circ N \to_{\beta\sigma} M' \circ N$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} M'$, then $M \circ N \to_{\beta\sigma} M' \circ N$.)

#### CompR:

$$
\begin{prooftree}
\AxiomC{$N \to_{\beta\sigma} N'$}
\RightLabel{CompR}
\UnaryInfC{$M \circ N \to_{\beta\sigma} M \circ N'$}
\end{prooftree}
$$

(If $N \to_{\beta\sigma} N'$, then $M \circ N \to_{\beta\sigma} M \circ N'$.)

#### Eop:

$$
\begin{prooftree}
\AxiomC{$M \to_{\beta\sigma} M'$}
\RightLabel{Eop}
\UnaryInfC{$\varepsilon(M) \to_{\beta\sigma} \varepsilon(M')$}
\end{prooftree}
$$

(If $M \to_{\beta\sigma} M'$, then $\varepsilon(M) \to_{\beta\sigma} \varepsilon(M')$.)


#### Definition (Relation $\to_{\beta\sigma}^*$)

The reflexive and transitive closure of $\to_{\beta\sigma}$ is written as $\to_{\beta\sigma}^{*}$.

Thus, $M \to_{\beta\sigma}^{*} N$ means that $M$ reduces to $N$ in zero or more steps.

## Informal Reading

The rules can be understood as describing how ordinary lambda-calculus computation is performed with an explicit, first-class environment-composition operator.

A beta reduction does not immediately substitute the argument into the body. Instead, it constructs an environment that records the binding of the formal parameter to the argument, and composes the body directly with that environment via `Comp` -- there is no need for an intervening $\varepsilon$ wrapper on the reduct, since environment composition is already a primitive of the syntax. `BetaClos` is the closure variant: when the abstraction has already been composed with an outer environment $L$ (i.e. $(\lambda x. M) \circ L$), that environment is carried along in the newly built extension. The `Comp` rule ($\mathrm{Comp}_{\varepsilon}$) is what turns an ordinary application $\varepsilon(M)N$ into an explicit composition $M \circ N$, handing the term over to the substitution rules below.

Variable lookup is performed by traversing environment extensions composed onto a variable. If the variable at the head of the composition is the one being referenced, the corresponding term is returned (`VarRef`). If it is different, the rule skips that binding and continues with the remaining environment (`VarSkip`).

The identity environment acts as a neutral element for composition: composing anything with the identity on either side leaves it unchanged (`IdL`, `IdR`), and composition itself is associative (`Assoc`).

The distribution rules explain how composition propagates through the structure of terms: it distributes over application (`DApp`) and over environment extension (`DExtn`), while a term already headed by $\varepsilon$ absorbs any further composition without change (`Eps-eps`) -- once a term is environment-abstracted, composing it with another environment does not alter it.
