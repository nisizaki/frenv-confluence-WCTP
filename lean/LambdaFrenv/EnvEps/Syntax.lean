import LambdaFrenv.Rewriting

/-!
# The auxiliary calculus `λ_EnvEps`

`λ_FREnv` writes environment *composition* and function *application* with
the same syntactic form `App (Eps M) N`.  That ambiguity makes the sigma
fragment of `λ_FREnv` resist a direct termination argument: the rules
`Assoc` and `DApp` overlap precisely because `App (Eps L) M` can be read
both ways.

Following the Isabelle development (`isabelle/EnvEps/EnvEps_Syntax.thy`),
we introduce the auxiliary calculus `λ_EnvEps`, whose syntax has a
primitive composition constructor `ETrm.comp`.  There `Assoc` acts on
`comp (comp M N) L` and `DApp` on `comp (app M N) L`, which are disjoint
shapes.

As in `LambdaFrenv.Basic` the calculus is parameterized by a type `V` of
variables and a type `C` of constants, and `ETrm.lam` / `ETrm.ext` take
their variable as plain first-order data — there is no binding machinery
and no alpha-equivalence quotient.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

/-- Terms of `λ_EnvEps`: the seven `λ_FREnv` forms plus `comp`. -/
inductive ETrm (V : Type u) (C : Type v) where
  | var : V → ETrm V C
  | const : C → ETrm V C
  | lam : V → ETrm V C → ETrm V C
  | app : ETrm V C → ETrm V C → ETrm V C
  | id : ETrm V C
  | ext : ETrm V C → V → ETrm V C → ETrm V C
  | eps : ETrm V C → ETrm V C
  | comp : ETrm V C → ETrm V C → ETrm V C

/-! ## The sigma fragment -/

/-- One-step sigma reduction of `λ_EnvEps`.

The nine root rules act on `comp`-headed terms and are pairwise
non-overlapping at the root; the eight remaining rules are the
compatibility (congruence) rules. -/
inductive SStep : ETrm V C → ETrm V C → Prop where
  | assoc :
      SStep (ETrm.comp (ETrm.comp M N) L) (ETrm.comp M (ETrm.comp N L))
  | idL :
      SStep (ETrm.comp ETrm.id M) M
  | idR :
      SStep (ETrm.comp M ETrm.id) M
  | dExt :
      SStep (ETrm.comp (ETrm.ext L x M) N)
        (ETrm.ext (ETrm.comp L N) x (ETrm.comp M N))
  | varRef :
      SStep (ETrm.comp (ETrm.var x) (ETrm.ext M x N)) M
  | varSkip : x ≠ y →
      SStep (ETrm.comp (ETrm.var y) (ETrm.ext M x N)) (ETrm.comp (ETrm.var y) N)
  | dApp :
      SStep (ETrm.comp (ETrm.app M N) L)
        (ETrm.app (ETrm.comp M L) (ETrm.comp N L))
  | epsEps :
      SStep (ETrm.comp (ETrm.eps M) N) (ETrm.eps M)
  | constC :
      SStep (ETrm.comp (ETrm.const c) N) (ETrm.const c)
  | appL : SStep M M' → SStep (ETrm.app M N) (ETrm.app M' N)
  | appR : SStep N N' → SStep (ETrm.app M N) (ETrm.app M N')
  | lam : SStep M M' → SStep (ETrm.lam x M) (ETrm.lam x M')
  | extL : SStep M M' → SStep (ETrm.ext M x N) (ETrm.ext M' x N)
  | extR : SStep N N' → SStep (ETrm.ext M x N) (ETrm.ext M x N')
  | compL : SStep M M' → SStep (ETrm.comp M N) (ETrm.comp M' N)
  | compR : SStep N N' → SStep (ETrm.comp M N) (ETrm.comp M N')
  | eps : SStep M M' → SStep (ETrm.eps M) (ETrm.eps M')

/-- Multi-step sigma reduction. -/
abbrev SSteps (M N : ETrm V C) : Prop := ReflTransGen SStep M N

/-! ## The beta fragment -/

/-- One-step beta reduction of `λ_EnvEps`: the three beta rules plus the
eight compatibility rules.

`compEps` is the rule that *reads* an application of an environment
abstraction as a composition; it is what makes the translation to
`λ_FREnv` collapse `comp` and `app (eps _) _`. -/
inductive BStep : ETrm V C → ETrm V C → Prop where
  | beta :
      BStep (ETrm.app (ETrm.lam x M) N) (ETrm.comp M (ETrm.ext N x ETrm.id))
  | betaClos :
      BStep (ETrm.app (ETrm.comp (ETrm.lam x M) L) N) (ETrm.comp M (ETrm.ext N x L))
  | compEps :
      BStep (ETrm.app (ETrm.eps M) N) (ETrm.comp M N)
  | appL : BStep M M' → BStep (ETrm.app M N) (ETrm.app M' N)
  | appR : BStep N N' → BStep (ETrm.app M N) (ETrm.app M N')
  | lam : BStep M M' → BStep (ETrm.lam x M) (ETrm.lam x M')
  | extL : BStep M M' → BStep (ETrm.ext M x N) (ETrm.ext M' x N)
  | extR : BStep N N' → BStep (ETrm.ext M x N) (ETrm.ext M x N')
  | compL : BStep M M' → BStep (ETrm.comp M N) (ETrm.comp M' N)
  | compR : BStep N N' → BStep (ETrm.comp M N) (ETrm.comp M N')
  | eps : BStep M M' → BStep (ETrm.eps M) (ETrm.eps M')

/-- Multi-step beta reduction. -/
abbrev BSteps (M N : ETrm V C) : Prop := ReflTransGen BStep M N

/-! ## The combined reduction -/

/-- One-step beta/sigma reduction: the union of the two fragments. -/
def BSStep (M N : ETrm V C) : Prop := BStep M N ∨ SStep M N

/-- Multi-step beta/sigma reduction. -/
abbrev BSSteps (M N : ETrm V C) : Prop := ReflTransGen BSStep M N

theorem BSStep.ofB {M N : ETrm V C} (h : BStep M N) : BSStep M N := Or.inl h

theorem BSStep.ofS {M N : ETrm V C} (h : SStep M N) : BSStep M N := Or.inr h

theorem BSSteps.ofB {M N : ETrm V C} (h : BSteps M N) : BSSteps M N :=
  ReflTransGen.mono (fun _ _ => BSStep.ofB) h

theorem BSSteps.ofS {M N : ETrm V C} (h : SSteps M N) : BSSteps M N :=
  ReflTransGen.mono (fun _ _ => BSStep.ofS) h

/-! ## Multi-step congruence rules

Each is an instance of `ReflTransGen.map`.
-/

namespace SSteps

variable {M M' N N' : ETrm V C}

theorem lam (h : SSteps M M') (x : V) : SSteps (ETrm.lam x M) (ETrm.lam x M') :=
  ReflTransGen.map (fun T => ETrm.lam x T) (fun _ _ => SStep.lam) h

theorem eps (h : SSteps M M') : SSteps (ETrm.eps M) (ETrm.eps M') :=
  ReflTransGen.map (fun T => ETrm.eps T) (fun _ _ => SStep.eps) h

theorem appL (h : SSteps M M') (N : ETrm V C) : SSteps (ETrm.app M N) (ETrm.app M' N) :=
  ReflTransGen.map (fun T => ETrm.app T N) (fun _ _ => SStep.appL) h

theorem appR (M : ETrm V C) (h : SSteps N N') : SSteps (ETrm.app M N) (ETrm.app M N') :=
  ReflTransGen.map (fun T => ETrm.app M T) (fun _ _ => SStep.appR) h

theorem extL (h : SSteps M M') (x : V) (N : ETrm V C) :
    SSteps (ETrm.ext M x N) (ETrm.ext M' x N) :=
  ReflTransGen.map (fun T => ETrm.ext T x N) (fun _ _ => SStep.extL) h

theorem extR (M : ETrm V C) (x : V) (h : SSteps N N') :
    SSteps (ETrm.ext M x N) (ETrm.ext M x N') :=
  ReflTransGen.map (fun T => ETrm.ext M x T) (fun _ _ => SStep.extR) h

theorem compL (h : SSteps M M') (N : ETrm V C) : SSteps (ETrm.comp M N) (ETrm.comp M' N) :=
  ReflTransGen.map (fun T => ETrm.comp T N) (fun _ _ => SStep.compL) h

theorem compR (M : ETrm V C) (h : SSteps N N') : SSteps (ETrm.comp M N) (ETrm.comp M N') :=
  ReflTransGen.map (fun T => ETrm.comp M T) (fun _ _ => SStep.compR) h

theorem app (h₁ : SSteps M M') (h₂ : SSteps N N') : SSteps (ETrm.app M N) (ETrm.app M' N') :=
  ReflTransGen.trans (appL h₁ N) (appR M' h₂)

theorem ext (h₁ : SSteps M M') (x : V) (h₂ : SSteps N N') :
    SSteps (ETrm.ext M x N) (ETrm.ext M' x N') :=
  ReflTransGen.trans (extL h₁ x N) (extR M' x h₂)

theorem comp (h₁ : SSteps M M') (h₂ : SSteps N N') : SSteps (ETrm.comp M N) (ETrm.comp M' N') :=
  ReflTransGen.trans (compL h₁ N) (compR M' h₂)

end SSteps

namespace BSteps

variable {M M' N N' : ETrm V C}

theorem lam (h : BSteps M M') (x : V) : BSteps (ETrm.lam x M) (ETrm.lam x M') :=
  ReflTransGen.map (fun T => ETrm.lam x T) (fun _ _ => BStep.lam) h

theorem eps (h : BSteps M M') : BSteps (ETrm.eps M) (ETrm.eps M') :=
  ReflTransGen.map (fun T => ETrm.eps T) (fun _ _ => BStep.eps) h

theorem appL (h : BSteps M M') (N : ETrm V C) : BSteps (ETrm.app M N) (ETrm.app M' N) :=
  ReflTransGen.map (fun T => ETrm.app T N) (fun _ _ => BStep.appL) h

theorem appR (M : ETrm V C) (h : BSteps N N') : BSteps (ETrm.app M N) (ETrm.app M N') :=
  ReflTransGen.map (fun T => ETrm.app M T) (fun _ _ => BStep.appR) h

theorem extL (h : BSteps M M') (x : V) (N : ETrm V C) :
    BSteps (ETrm.ext M x N) (ETrm.ext M' x N) :=
  ReflTransGen.map (fun T => ETrm.ext T x N) (fun _ _ => BStep.extL) h

theorem extR (M : ETrm V C) (x : V) (h : BSteps N N') :
    BSteps (ETrm.ext M x N) (ETrm.ext M x N') :=
  ReflTransGen.map (fun T => ETrm.ext M x T) (fun _ _ => BStep.extR) h

theorem compL (h : BSteps M M') (N : ETrm V C) : BSteps (ETrm.comp M N) (ETrm.comp M' N) :=
  ReflTransGen.map (fun T => ETrm.comp T N) (fun _ _ => BStep.compL) h

theorem compR (M : ETrm V C) (h : BSteps N N') : BSteps (ETrm.comp M N) (ETrm.comp M N') :=
  ReflTransGen.map (fun T => ETrm.comp M T) (fun _ _ => BStep.compR) h

theorem app (h₁ : BSteps M M') (h₂ : BSteps N N') : BSteps (ETrm.app M N) (ETrm.app M' N') :=
  ReflTransGen.trans (appL h₁ N) (appR M' h₂)

theorem ext (h₁ : BSteps M M') (x : V) (h₂ : BSteps N N') :
    BSteps (ETrm.ext M x N) (ETrm.ext M' x N') :=
  ReflTransGen.trans (extL h₁ x N) (extR M' x h₂)

theorem comp (h₁ : BSteps M M') (h₂ : BSteps N N') : BSteps (ETrm.comp M N) (ETrm.comp M' N') :=
  ReflTransGen.trans (compL h₁ N) (compR M' h₂)

end BSteps

namespace BSSteps

variable {M M' N N' : ETrm V C}

theorem lam (h : BSSteps M M') (x : V) : BSSteps (ETrm.lam x M) (ETrm.lam x M') :=
  ReflTransGen.map (fun T => ETrm.lam x T)
    (fun _ _ h => h.imp (fun hb => BStep.lam hb) (fun hs => SStep.lam hs)) h

theorem eps (h : BSSteps M M') : BSSteps (ETrm.eps M) (ETrm.eps M') :=
  ReflTransGen.map (fun T => ETrm.eps T)
    (fun _ _ h => h.imp (fun hb => BStep.eps hb) (fun hs => SStep.eps hs)) h

theorem appL (h : BSSteps M M') (N : ETrm V C) : BSSteps (ETrm.app M N) (ETrm.app M' N) :=
  ReflTransGen.map (fun T => ETrm.app T N)
    (fun _ _ h => h.imp (fun hb => BStep.appL hb) (fun hs => SStep.appL hs)) h

theorem appR (M : ETrm V C) (h : BSSteps N N') : BSSteps (ETrm.app M N) (ETrm.app M N') :=
  ReflTransGen.map (fun T => ETrm.app M T)
    (fun _ _ h => h.imp (fun hb => BStep.appR hb) (fun hs => SStep.appR hs)) h

theorem extL (h : BSSteps M M') (x : V) (N : ETrm V C) :
    BSSteps (ETrm.ext M x N) (ETrm.ext M' x N) :=
  ReflTransGen.map (fun T => ETrm.ext T x N)
    (fun _ _ h => h.imp (fun hb => BStep.extL hb) (fun hs => SStep.extL hs)) h

theorem extR (M : ETrm V C) (x : V) (h : BSSteps N N') :
    BSSteps (ETrm.ext M x N) (ETrm.ext M x N') :=
  ReflTransGen.map (fun T => ETrm.ext M x T)
    (fun _ _ h => h.imp (fun hb => BStep.extR hb) (fun hs => SStep.extR hs)) h

theorem compL (h : BSSteps M M') (N : ETrm V C) : BSSteps (ETrm.comp M N) (ETrm.comp M' N) :=
  ReflTransGen.map (fun T => ETrm.comp T N)
    (fun _ _ h => h.imp (fun hb => BStep.compL hb) (fun hs => SStep.compL hs)) h

theorem compR (M : ETrm V C) (h : BSSteps N N') : BSSteps (ETrm.comp M N) (ETrm.comp M N') :=
  ReflTransGen.map (fun T => ETrm.comp M T)
    (fun _ _ h => h.imp (fun hb => BStep.compR hb) (fun hs => SStep.compR hs)) h

theorem app (h₁ : BSSteps M M') (h₂ : BSSteps N N') :
    BSSteps (ETrm.app M N) (ETrm.app M' N') :=
  ReflTransGen.trans (appL h₁ N) (appR M' h₂)

theorem ext (h₁ : BSSteps M M') (x : V) (h₂ : BSSteps N N') :
    BSSteps (ETrm.ext M x N) (ETrm.ext M' x N') :=
  ReflTransGen.trans (extL h₁ x N) (extR M' x h₂)

theorem comp (h₁ : BSSteps M M') (h₂ : BSSteps N N') :
    BSSteps (ETrm.comp M N) (ETrm.comp M' N') :=
  ReflTransGen.trans (compL h₁ N) (compR M' h₂)

end BSSteps

end EnvEps

end LambdaFrenv
