# Proof map and scope

## Target property

For the combined beta/sigma reduction of FREnv, full confluence means

```text
P ->* Q1 and P ->* Q2  implies  there is L with Q1 ->* L and Q2 ->* L.
```

The two branches may contain arbitrarily many finite steps. Local confluence, whose branches each start with one step, is a different property; local confluence alone is not the argument used to obtain the final result.

## Isabelle dependency route

The authoritative final declaration is `frenv_beta_sigma_confluent` in
[FREnv_Full_Confluence_Via_Translation.thy](../isabelle/EnvEps/FREnv_Full_Confluence_Via_Translation.thy).

1. **FREnv definitions.** `FREnv_Syntax`, `FREnv_Sigma`, and `FREnv_BetaSigma` define the target language and reduction. `FREnv_BetaSigma_Congruence` provides multi-step congruence. The remaining FREnv theories separately establish local confluence.
2. **Auxiliary EnvEps calculus.** `EnvEps_Syntax`, `EnvEps_Sigma`, and `EnvEps_BetaSigma` define an explicit composition constructor in addition to the other term forms.
3. **Sigma normalization.** The term-length measure, decrease and termination lemmas, peak analyses, and Newman's lemma establish sigma confluence. Subsequent theories define and characterize sigma-normal forms. `Newmans_Lemma` uses the vendored AFP theorem.
4. **Parallel reduction.** Reflexivity, simulation, soundness, complete development, composition compatibility, and the triangle property support parallel-reduction confluence and beta-over-sigma confluence.
5. **Full EnvEps confluence.** `EnvEps_Beta_Sigma_Full_Confluence.beta_sigma_confluent` combines the normalization and parallel-reduction arguments.
6. **Translation.** `EnvEps_FREnv_Translation` maps EnvEps terms to FREnv. Surjectivity provides a preimage of an arbitrary FREnv term. Inversion, simulation, single-step lifting, and multi-step lifting relate the reduction paths.
7. **Transfer.** Lift both FREnv paths to EnvEps, use EnvEps confluence to join the witnesses, and translate the joining paths back. Multi-step lifting uses the already established EnvEps confluence theorem; there is no circular reliance on the final FREnv theorem.

The [session configuration](../isabelle/EnvEps/ROOT) lists the formal theories; Isabelle follows their actual imports. The [mathematical notes](../isabelle/docs/) give more detailed English explanations. The active FREnv and EnvEps developments are included in full so that this proof route and the related local-confluence result can both be checked. The abandoned historical FREnv development is excluded; only its required AFP library snapshots are retained under `vendor/`.

For a file-by-file view, see the [application theory index](theory-index.md), which lists all 48 theories and their direct imports.

## Lean development

[Basic.lean](../lean/LambdaFrenv/Basic.lean) defines the term type, beta/sigma reduction, its reflexive-transitive closure, and generic confluence predicates. [Par.lean](../lean/LambdaFrenv/Par.lean) defines parallel reduction and proves its embedding and simulation properties as well as closure congruence.

The Lean development now proves full confluence, `LambdaFrenv.frenv_beta_sigma_confluent`, along the same mathematical route as the Isabelle one: an auxiliary calculus `λ_EnvEps` with a primitive composition constructor ([EnvEps/Syntax.lean](../lean/LambdaFrenv/EnvEps/Syntax.lean)), sigma termination via a multiplicative length measure ([EnvEps/Length.lean](../lean/LambdaFrenv/EnvEps/Length.lean)), local confluence and Newman's lemma ([EnvEps/SigmaConfluence.lean](../lean/LambdaFrenv/EnvEps/SigmaConfluence.lean), [Rewriting.lean](../lean/LambdaFrenv/Rewriting.lean)), sigma-normal forms ([EnvEps/NormalForm.lean](../lean/LambdaFrenv/EnvEps/NormalForm.lean)), the parallel-beta diamond property ([EnvEps/PStep.lean](../lean/LambdaFrenv/EnvEps/PStep.lean)), composition compatibility ([EnvEps/Compat.lean](../lean/LambdaFrenv/EnvEps/Compat.lean)), beta over sigma ([EnvEps/BetaOverSigma.lean](../lean/LambdaFrenv/EnvEps/BetaOverSigma.lean)), and the translation with its lifting lemma ([Translation.lean](../lean/LambdaFrenv/Translation.lean)).

The `ParStronglyConfluent` target stated at the end of `Par.lean` is **false**, and [ParNotStrong.lean](../lean/LambdaFrenv/ParNotStrong.lean) proves its negation: on the associativity pentagon the two `Assoc` reducts have disjoint sets of one-step parallel reducts. The `overlap...` declarations remain definitions of propositions and are not used. This is why the Lean proof, like the Isabelle one, must go through sigma normalization rather than a direct diamond property.

## Mizar development

The Mizar development proves the same statement as `FRENV_5:8`, following the same route again. It is laid out as fourteen articles under [mizar/text/](../mizar/text/), in dependency order: the parse-tree syntax of `λ_EnvEps` with its length measure, sigma reduction and termination (`enveps_1`); multi-step congruence and inversion (`enveps_2`, `enveps_3`); the critical-pair analysis, local confluence and sigma confluence (`enveps_4`); sigma-normal forms and the normal form operator (`enveps_5`); beta and beta/sigma reduction (`enveps_6`); parallel reduction, the triangle property and confluence of beta (`enveps_7`); composition compatibility and the key lemma (`enveps_8`); Hardin's interpretation method (`enveps_9`); the syntax and reduction of `λ_FREnv` (`frenv_1`, `frenv_2`); and the translation, simulation and lifting (`frenv_3`–`frenv_5`).

Two things differ from the other two developments at the level of the proof assistant rather than the mathematics. Mizar has no inductive datatypes, so terms are parse trees over a tagged symbol alphabet built with `DTCONSTR`, and every reduction relation is defined as the least relation closed under its rules, with a separately proved inversion lemma. And Newman's lemma, the normal form operator and the confluence predicates come from the MML article `REWRITE1` rather than being developed here or vendored.

The triangle property is stated in existential form — for every term there is a term absorbing all of its parallel reducts — because `DTCONSTR`'s structural recursion cannot express the complete development: the beta-closure rule inspects a grandchild of the node.

## Differences between the encodings

| Aspect | Isabelle | Lean | Mizar |
|---|---|---|---|
| Variable names | Strings | Parameter type `V` | Parameter set `V`, any non-empty set |
| Primitive constants | None | Parameter type `C`, constructor `Trm.const`, and a constant reduction rule | None |
| Bindings in raw syntax | Names are ordinary datatype arguments | Variable parameters are ordinary datatype arguments | Binder symbols are indexed by the variable, so the name is part of the node |
| Auxiliary EnvEps calculus | Included | Included (`LambdaFrenv/EnvEps/`) | Included (`mizar/text/enveps_*.miz`) |
| Main route | Sigma normalization, parallel reduction on the auxiliary side, and transfer | The same route, with parallel beta on all terms and the diamond property obtained from a complete development | The same route, with the triangle property stated in existential form instead of a complete-development function |
| Final confluence result | Theorem supplied | Theorem supplied | Theorem supplied |

There is no machine-checked equivalence theorem between these encodings in this artifact. Even restricting Lean's constants type to an empty type does not by itself establish such an equivalence; the representations and relations would still need a proved correspondence.

## Interpreting verification

An Isabelle build with `quick_and_dirty=false` checks the included proofs rather than accepting skipped proof commands. A Lean build checks all declarations in the default library target; the extra audit displays the axiom dependencies of its supporting theorems. A Mizar run checks every inference of every article, and an empty `.err` file is the only success criterion: there is no `sorry` and no way for an article to introduce an axiom. None of the three checks the prose in Markdown files. See [verification.md](verification.md) for the actual build record.
