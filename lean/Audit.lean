import LambdaFrenv

-- These are proved supporting theorems; inspect their axiom dependencies.
#print axioms LambdaFrenv.ReflTransGen.trans
#print axioms LambdaFrenv.ReflTransGen.single
#print axioms LambdaFrenv.BetaSigmaSteps.lam
#print axioms LambdaFrenv.BetaSigmaSteps.appL
#print axioms LambdaFrenv.BetaSigmaSteps.appR
#print axioms LambdaFrenv.BetaSigmaSteps.extL
#print axioms LambdaFrenv.BetaSigmaSteps.extR
#print axioms LambdaFrenv.BetaSigmaSteps.eps
#print axioms LambdaFrenv.ParStep.embed
#print axioms LambdaFrenv.ParStep.sim

-- This is a definition of an open target proposition, NOT its proof.
#print LambdaFrenv.ParStronglyConfluent
