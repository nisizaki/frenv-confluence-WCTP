import LambdaFrenv

/-! Audit of the Lean development.

Every theorem below is *proved*.  `#print axioms` shows the axiom
dependencies; none of them mentions `sorryAx`, so no proof is admitted.
`propext`, `Classical.choice` and `Quot.sound` are Lean's three standard
axioms — `Classical.choice` enters through the sigma-normal-form operator
`snf`, which is defined by choosing a normal form. -/

-- The main result: full beta/sigma confluence of λ_FREnv.
#print axioms LambdaFrenv.frenv_beta_sigma_confluent
#print axioms LambdaFrenv.frenv_beta_sigma_joinable
#print axioms LambdaFrenv.frenv_locally_confluent

-- Confluence of the auxiliary calculus λ_EnvEps and its ingredients.
#print axioms LambdaFrenv.EnvEps.bsstep_confluent
#print axioms LambdaFrenv.EnvEps.sstep_confluent
#print axioms LambdaFrenv.EnvEps.sstep_locally_confluent
#print axioms LambdaFrenv.EnvEps.sstep_sn
#print axioms LambdaFrenv.EnvEps.pstep_diamond
#print axioms LambdaFrenv.EnvEps.cc
#print axioms LambdaFrenv.EnvEps.key
#print axioms LambdaFrenv.EnvEps.bos_diamond

-- Abstract rewriting infrastructure.
#print axioms LambdaFrenv.newman
#print axioms LambdaFrenv.Diamond.confluent

-- Translation and lifting.
#print axioms LambdaFrenv.tr_incl
#print axioms LambdaFrenv.tr_bssteps
#print axioms LambdaFrenv.lift1
#print axioms LambdaFrenv.liftMulti

-- Supporting theorems of the imported revision.
#print axioms LambdaFrenv.ReflTransGen.trans
#print axioms LambdaFrenv.ReflTransGen.single
#print axioms LambdaFrenv.ParStep.embed
#print axioms LambdaFrenv.ParStep.sim

-- `ParStronglyConfluent`, announced as the next milestone by the imported
-- revision, is FALSE: parallel reduction of λ_FREnv has no diamond
-- property, because Assoc is confluent but never strongly confluent.
#print LambdaFrenv.ParStronglyConfluent
#print axioms LambdaFrenv.not_parStronglyConfluent
