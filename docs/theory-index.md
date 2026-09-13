# Isabelle application theory index

The table lists the 48 active application theories and their direct imports. Isabelle resolves the complete dependency graph during the session build. The final theorem and the proof route are explained in [proof-map.md](proof-map.md).

## FREnv

| Theory | Direct imports |
|---|---|
| [FREnv_BetaSigma](../isabelle/FREnv/FREnv_BetaSigma.thy) | [FREnv_Sigma](../isabelle/FREnv/FREnv_Sigma.thy) |
| [FREnv_BetaSigma_Assoc_Peak](../isabelle/FREnv/FREnv_BetaSigma_Assoc_Peak.thy) | [FREnv_BetaSigma_Congruence](../isabelle/FREnv/FREnv_BetaSigma_Congruence.thy) |
| [FREnv_BetaSigma_Congruence](../isabelle/FREnv/FREnv_BetaSigma_Congruence.thy) | [FREnv_BetaSigma](../isabelle/FREnv/FREnv_BetaSigma.thy) |
| [FREnv_BetaSigma_Congruence_Peaks](../isabelle/FREnv/FREnv_BetaSigma_Congruence_Peaks.thy) | [FREnv_BetaSigma_Root_Peaks](../isabelle/FREnv/FREnv_BetaSigma_Root_Peaks.thy) |
| [FREnv_BetaSigma_DApp_Peak](../isabelle/FREnv/FREnv_BetaSigma_DApp_Peak.thy) | [FREnv_BetaSigma_Congruence](../isabelle/FREnv/FREnv_BetaSigma_Congruence.thy) |
| [FREnv_BetaSigma_Local_Confluence](../isabelle/FREnv/FREnv_BetaSigma_Local_Confluence.thy) | [FREnv_BetaSigma_Congruence_Peaks](../isabelle/FREnv/FREnv_BetaSigma_Congruence_Peaks.thy) |
| [FREnv_BetaSigma_Root_Peaks](../isabelle/FREnv/FREnv_BetaSigma_Root_Peaks.thy) | [FREnv_BetaSigma_Assoc_Peak](../isabelle/FREnv/FREnv_BetaSigma_Assoc_Peak.thy), [FREnv_BetaSigma_DApp_Peak](../isabelle/FREnv/FREnv_BetaSigma_DApp_Peak.thy) |
| [FREnv_Sigma](../isabelle/FREnv/FREnv_Sigma.thy) | [FREnv_Syntax](../isabelle/FREnv/FREnv_Syntax.thy) |
| [FREnv_Syntax](../isabelle/FREnv/FREnv_Syntax.thy) | `Main` |

## EnvEps

| Theory | Direct imports |
|---|---|
| [Diamond_Implies_Confluence](../isabelle/EnvEps/Diamond_Implies_Confluence.thy) | `Main` |
| [EnvEps_Beta_Normal_Form_Simulation](../isabelle/EnvEps/EnvEps_Beta_Normal_Form_Simulation.thy) | [EnvEps_Beta_Over_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma_Congruence.thy), [EnvEps_Sigma_Length_Decrease](../isabelle/EnvEps/EnvEps_Sigma_Length_Decrease.thy), [EnvEps_Sigma_Nf_Equiv](../isabelle/EnvEps/EnvEps_Sigma_Nf_Equiv.thy), [EnvEps_Parallel_Reduction_Simulation](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Simulation.thy), [EnvEps_Parallel_Reduction_Soundness](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Soundness.thy), [EnvEps_Parallel_Reduction_Composition_Compatibility](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Composition_Compatibility.thy) |
| [EnvEps_Beta_Over_Sigma](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma.thy) | [EnvEps_Beta_Step](../isabelle/EnvEps/EnvEps_Beta_Step.thy), [EnvEps_Sigma_Normal_Form_Grammar](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form_Grammar.thy) |
| [EnvEps_Beta_Over_Sigma_Confluence](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma_Confluence.thy) | [EnvEps_Parallel_Reduction_Confluence](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Confluence.thy), [EnvEps_Parallel_Reduction_Simulation](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Simulation.thy), [EnvEps_Parallel_Reduction_Soundness](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Soundness.thy) |
| [EnvEps_Beta_Over_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma_Congruence.thy) | [EnvEps_Beta_Over_Sigma](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma.thy), [EnvEps_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Sigma_Congruence.thy) |
| [EnvEps_Beta_Sigma_Full_Confluence](../isabelle/EnvEps/EnvEps_Beta_Sigma_Full_Confluence.thy) | [EnvEps_Beta_Over_Sigma_Confluence](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma_Confluence.thy), [EnvEps_Beta_Normal_Form_Simulation](../isabelle/EnvEps/EnvEps_Beta_Normal_Form_Simulation.thy) |
| [EnvEps_Beta_Step](../isabelle/EnvEps/EnvEps_Beta_Step.thy) | [EnvEps_BetaSigma](../isabelle/EnvEps/EnvEps_BetaSigma.thy) |
| [EnvEps_BetaSigma](../isabelle/EnvEps/EnvEps_BetaSigma.thy) | [EnvEps_Sigma](../isabelle/EnvEps/EnvEps_Sigma.thy) |
| [EnvEps_BetaSigma_Congruence](../isabelle/EnvEps/EnvEps_BetaSigma_Congruence.thy) | [EnvEps_BetaSigma](../isabelle/EnvEps/EnvEps_BetaSigma.thy) |
| [EnvEps_Complete_Development](../isabelle/EnvEps/EnvEps_Complete_Development.thy) | [EnvEps_Sigma_Normal_Form](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form.thy) |
| [EnvEps_FREnv_Translation](../isabelle/EnvEps/EnvEps_FREnv_Translation.thy) | [EnvEps_Syntax](../isabelle/EnvEps/EnvEps_Syntax.thy), [FREnv_Syntax](../isabelle/FREnv/FREnv_Syntax.thy) |
| [EnvEps_FREnv_Translation_Inversion](../isabelle/EnvEps/EnvEps_FREnv_Translation_Inversion.thy) | [EnvEps_FREnv_Translation](../isabelle/EnvEps/EnvEps_FREnv_Translation.thy) |
| [EnvEps_FREnv_Translation_Lifting](../isabelle/EnvEps/EnvEps_FREnv_Translation_Lifting.thy) | [EnvEps_FREnv_Translation_Simulation](../isabelle/EnvEps/EnvEps_FREnv_Translation_Simulation.thy), [EnvEps_BetaSigma_Congruence](../isabelle/EnvEps/EnvEps_BetaSigma_Congruence.thy), [EnvEps_FREnv_Translation_Inversion](../isabelle/EnvEps/EnvEps_FREnv_Translation_Inversion.thy) |
| [EnvEps_FREnv_Translation_Multi_Step_Lifting](../isabelle/EnvEps/EnvEps_FREnv_Translation_Multi_Step_Lifting.thy) | [EnvEps_FREnv_Translation_Lifting](../isabelle/EnvEps/EnvEps_FREnv_Translation_Lifting.thy), [EnvEps_Beta_Sigma_Full_Confluence](../isabelle/EnvEps/EnvEps_Beta_Sigma_Full_Confluence.thy) |
| [EnvEps_FREnv_Translation_Simulation](../isabelle/EnvEps/EnvEps_FREnv_Translation_Simulation.thy) | [EnvEps_FREnv_Translation](../isabelle/EnvEps/EnvEps_FREnv_Translation.thy), [EnvEps_BetaSigma](../isabelle/EnvEps/EnvEps_BetaSigma.thy), [FREnv_BetaSigma_Congruence](../isabelle/FREnv/FREnv_BetaSigma_Congruence.thy) |
| [EnvEps_FREnv_Translation_Surjective](../isabelle/EnvEps/EnvEps_FREnv_Translation_Surjective.thy) | [EnvEps_FREnv_Translation](../isabelle/EnvEps/EnvEps_FREnv_Translation.thy) |
| [EnvEps_Parallel_Reduction](../isabelle/EnvEps/EnvEps_Parallel_Reduction.thy) | [EnvEps_Sigma_Normal_Form_Grammar](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form_Grammar.thy) |
| [EnvEps_Parallel_Reduction_Composition_Compatibility](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Composition_Compatibility.thy) | [EnvEps_Parallel_Reduction_Reflexivity](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Reflexivity.thy), [EnvEps_Sigma_Nf_Equiv](../isabelle/EnvEps/EnvEps_Sigma_Nf_Equiv.thy) |
| [EnvEps_Parallel_Reduction_Confluence](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Confluence.thy) | [EnvEps_Parallel_Reduction_Triangle_Property](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Triangle_Property.thy), [EnvEps_Parallel_Reduction_Reflexivity](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Reflexivity.thy), [Diamond_Implies_Confluence](../isabelle/EnvEps/Diamond_Implies_Confluence.thy) |
| [EnvEps_Parallel_Reduction_Reflexivity](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Reflexivity.thy) | [EnvEps_Parallel_Reduction](../isabelle/EnvEps/EnvEps_Parallel_Reduction.thy) |
| [EnvEps_Parallel_Reduction_Simulation](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Simulation.thy) | [EnvEps_Parallel_Reduction_Reflexivity](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Reflexivity.thy), [EnvEps_Beta_Over_Sigma](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma.thy), [EnvEps_Sigma_Nf_Equiv](../isabelle/EnvEps/EnvEps_Sigma_Nf_Equiv.thy), [EnvEps_Parallel_Reduction_Composition_Compatibility](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Composition_Compatibility.thy) |
| [EnvEps_Parallel_Reduction_Soundness](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Soundness.thy) | [EnvEps_Parallel_Reduction_Reflexivity](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Reflexivity.thy), [EnvEps_Beta_Over_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Beta_Over_Sigma_Congruence.thy), [EnvEps_Sigma_Nf_Equiv](../isabelle/EnvEps/EnvEps_Sigma_Nf_Equiv.thy) |
| [EnvEps_Parallel_Reduction_Triangle_Property](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Triangle_Property.thy) | [EnvEps_Complete_Development](../isabelle/EnvEps/EnvEps_Complete_Development.thy), [EnvEps_Parallel_Reduction_Composition_Compatibility](../isabelle/EnvEps/EnvEps_Parallel_Reduction_Composition_Compatibility.thy) |
| [EnvEps_Sigma](../isabelle/EnvEps/EnvEps_Sigma.thy) | [EnvEps_Syntax](../isabelle/EnvEps/EnvEps_Syntax.thy) |
| [EnvEps_Sigma_Assoc_Peak](../isabelle/EnvEps/EnvEps_Sigma_Assoc_Peak.thy) | [EnvEps_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Sigma_Congruence.thy) |
| [EnvEps_Sigma_Confluence](../isabelle/EnvEps/EnvEps_Sigma_Confluence.thy) | [EnvEps_Sigma_Termination](../isabelle/EnvEps/EnvEps_Sigma_Termination.thy), [EnvEps_Sigma_Local_Confluence](../isabelle/EnvEps/EnvEps_Sigma_Local_Confluence.thy), [Newmans_Lemma](../isabelle/EnvEps/Newmans_Lemma.thy) |
| [EnvEps_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Sigma_Congruence.thy) | [EnvEps_Sigma](../isabelle/EnvEps/EnvEps_Sigma.thy) |
| [EnvEps_Sigma_Inner_Peaks](../isabelle/EnvEps/EnvEps_Sigma_Inner_Peaks.thy) | [EnvEps_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Sigma_Congruence.thy) |
| [EnvEps_Sigma_Length_Decrease](../isabelle/EnvEps/EnvEps_Sigma_Length_Decrease.thy) | [EnvEps_Sigma](../isabelle/EnvEps/EnvEps_Sigma.thy), [EnvEps_Term_Length](../isabelle/EnvEps/EnvEps_Term_Length.thy) |
| [EnvEps_Sigma_Local_Confluence](../isabelle/EnvEps/EnvEps_Sigma_Local_Confluence.thy) | [EnvEps_Sigma_Root_Peaks](../isabelle/EnvEps/EnvEps_Sigma_Root_Peaks.thy) |
| [EnvEps_Sigma_Nf_Equiv](../isabelle/EnvEps/EnvEps_Sigma_Nf_Equiv.thy) | [EnvEps_Sigma_Normal_Form_Grammar](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form_Grammar.thy), [EnvEps_Sigma_Congruence](../isabelle/EnvEps/EnvEps_Sigma_Congruence.thy) |
| [EnvEps_Sigma_Normal_Form](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form.thy) | [EnvEps_Sigma_Confluence](../isabelle/EnvEps/EnvEps_Sigma_Confluence.thy) |
| [EnvEps_Sigma_Normal_Form_Grammar](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form_Grammar.thy) | [EnvEps_Sigma_Normal_Form](../isabelle/EnvEps/EnvEps_Sigma_Normal_Form.thy) |
| [EnvEps_Sigma_Root_Peaks](../isabelle/EnvEps/EnvEps_Sigma_Root_Peaks.thy) | [EnvEps_Sigma_Assoc_Peak](../isabelle/EnvEps/EnvEps_Sigma_Assoc_Peak.thy), [EnvEps_Sigma_Inner_Peaks](../isabelle/EnvEps/EnvEps_Sigma_Inner_Peaks.thy) |
| [EnvEps_Sigma_Termination](../isabelle/EnvEps/EnvEps_Sigma_Termination.thy) | [EnvEps_Sigma_Length_Decrease](../isabelle/EnvEps/EnvEps_Sigma_Length_Decrease.thy) |
| [EnvEps_Syntax](../isabelle/EnvEps/EnvEps_Syntax.thy) | `Main` |
| [EnvEps_Term_Length](../isabelle/EnvEps/EnvEps_Term_Length.thy) | [EnvEps_Syntax](../isabelle/EnvEps/EnvEps_Syntax.thy) |
| [FREnv_Full_Confluence_Via_Translation](../isabelle/EnvEps/FREnv_Full_Confluence_Via_Translation.thy) | [EnvEps_FREnv_Translation_Multi_Step_Lifting](../isabelle/EnvEps/EnvEps_FREnv_Translation_Multi_Step_Lifting.thy), [EnvEps_FREnv_Translation_Surjective](../isabelle/EnvEps/EnvEps_FREnv_Translation_Surjective.thy), [EnvEps_Beta_Sigma_Full_Confluence](../isabelle/EnvEps/EnvEps_Beta_Sigma_Full_Confluence.thy) |
| [Newmans_Lemma](../isabelle/EnvEps/Newmans_Lemma.thy) | [Abstract_Rewriting](../isabelle/vendor/Abstract-Rewriting/Abstract_Rewriting.thy) |
