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

The final section of `Par.lean` defines `ParStronglyConfluent` and root-overlap obligations as propositions. None of these definitions asserts that the proposition is true. The supplied revision does not include a full-confluence proof, a strong-confluence proof for parallel reduction, or a translation-based EnvEps development.

## Differences between the encodings

| Aspect | Isabelle | Lean |
|---|---|---|
| Variable names | Strings | Parameter type `V` |
| Primitive constants | None | Parameter type `C`, constructor `Trm.const`, and a constant reduction rule |
| Bindings in raw syntax | Names are ordinary datatype arguments | Variable parameters are ordinary datatype arguments |
| Auxiliary EnvEps calculus | Included | Not included |
| Main route | Sigma normalization, parallel reduction on the auxiliary side, and transfer | Direct FREnv parallel-reduction infrastructure |
| Final confluence result | Theorem supplied | Open target only |

There is no machine-checked equivalence theorem between these two encodings in this artifact. Even restricting Lean's constants type to an empty type does not by itself establish such an equivalence; the representations and relations would still need a proved correspondence.

## Interpreting verification

An Isabelle build with `quick_and_dirty=false` checks the included proofs rather than accepting skipped proof commands. A Lean build checks all declarations in the default library target; the extra audit displays the axiom dependencies of its supporting theorems. Neither compiler checks the prose in Markdown files. See [verification.md](verification.md) for the actual build record.
