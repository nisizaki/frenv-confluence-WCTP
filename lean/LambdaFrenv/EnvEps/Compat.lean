import LambdaFrenv.EnvEps.PStep

/-!
# Composition compatibility

The single hard lemma of the beta-over-sigma argument
(`isabelle/EnvEps/EnvEps_Parallel_Reduction_Composition_Compatibility.thy`):

> if `U` and `W` are sigma-normal and `U ⇒β S₁`, `W ⇒β S₂`, then
> `snf (comp U W)` makes one parallel beta step to some `S` with
> `snf S = snf (comp S₁ S₂)`.

`snf (comp U W)` is *not* structurally related to `U` and `W`, so the
proof is a case analysis on the grammar of sigma-normal forms, by strong
induction on the length measure `elen (comp U W)`.
-/

namespace LambdaFrenv

namespace EnvEps

universe u v

variable {V : Type u} {C : Type v}

/-! ## `snf` congruences used throughout -/

theorem snfComp {A₁ A₂ B₁ B₂ : ETrm V C} (hA : snf A₁ = snf A₂)
    (hB : snf B₁ = snf B₂) : snf (ETrm.comp A₁ B₁) = snf (ETrm.comp A₂ B₂) := by
  rw [snf_comp A₁ B₁, snf_comp A₂ B₂, hA, hB]

theorem snfCompExt {P₁ P₂ B₁ B₂ L₁ L₂ : ETrm V C} {x : V}
    (hP : snf P₁ = snf P₂) (hB : snf B₁ = snf B₂) (hL : snf L₁ = snf L₂) :
    snf (ETrm.comp P₁ (ETrm.ext B₁ x L₁)) = snf (ETrm.comp P₂ (ETrm.ext B₂ x L₂)) :=
  snfComp hP (by rw [snf_ext, snf_ext, hB, hL])

/-- Pushing a composition into a `betaClos` contractum. -/
private theorem snfClosTarget (P B L S : ETrm V C) (x : V) :
    snf (ETrm.comp (ETrm.comp P (ETrm.ext B x L)) S)
      = snf (ETrm.comp P (ETrm.ext (ETrm.comp B S) x (ETrm.comp L S))) :=
  snf_congr (ReflTransGen.tail (ReflTransGen.single SStep.assoc) (SStep.compR SStep.dExt))

private theorem elen_var_snf_lt {x : V} (L W : ETrm V C) :
    elen (ETrm.comp (ETrm.var x) (snf (ETrm.comp L W)))
      < elen (ETrm.comp (ETrm.comp (ETrm.var x) L) W) := by
  have hle : elen (snf (ETrm.comp L W)) ≤ elen (ETrm.comp L W) := SSteps.elen_le (snf_steps _)
  have e1 : elen (ETrm.comp L W) = elen L * (elen W + 1) := by simp only [elen]
  have e2 : elen (ETrm.comp (ETrm.comp (ETrm.var x) L) W)
      = elen L * (elen W + 1) + (elen W + 1) := by
    simp only [elen]
    rw [Nat.one_mul, Nat.add_mul, Nat.one_mul]
  have e3 : elen (ETrm.comp (ETrm.var x) (snf (ETrm.comp L W)))
      = elen (snf (ETrm.comp L W)) + 1 := by simp only [elen]; omega
  have hw : 0 < elen W := elen_pos W
  omega

/-! ## The statement, bounded by the measure -/

/-- Composition compatibility for all pairs of measure at most `n`. -/
private abbrev CCAt (V : Type u) (C : Type v) (n : Nat) : Prop :=
  ∀ (U W S₁ S₂ : ETrm V C), elen (ETrm.comp U W) ≤ n → SNormal U → SNormal W →
    PStep U S₁ → PStep W S₂ →
    ∃ S, PStep (snf (ETrm.comp U W)) S ∧ snf S = snf (ETrm.comp S₁ S₂)

/-! ## The individual cases -/

private theorem ccApp {n : Nat} (ihn : CCAt V C n) {A B A' B' W S₂ : ETrm V C}
    (hn : elen (ETrm.comp (ETrm.app A B) W) ≤ n + 1)
    (hAn : SNormal A) (hBn : SNormal B) (hW : SNormal W)
    (hA' : PStep A A') (hB' : PStep B B') (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.app A B) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.app A' B') S₂) := by
  have hmA : elen (ETrm.comp A W) ≤ n := by
    have h := elen_comp_lt_left (X := A) (U := ETrm.app A B) W (elen_lt_app_left A B)
    omega
  have hmB : elen (ETrm.comp B W) ≤ n := by
    have h := elen_comp_lt_left (X := B) (U := ETrm.app A B) W (elen_lt_app_right A B)
    omega
  obtain ⟨T₁, hT₁, eT₁⟩ := ihn A W A' S₂ hmA hAn hW hA' h₂
  obtain ⟨T₂, hT₂, eT₂⟩ := ihn B W B' S₂ hmB hBn hW hB' h₂
  refine ⟨ETrm.app T₁ T₂, ?_, ?_⟩
  · rw [snf_step (SStep.dApp (M := A) (N := B) (L := W)), snf_app]
    exact PStep.app hT₁ hT₂
  · rw [snf_app, snf_step (SStep.dApp (M := A') (N := B') (L := S₂)), snf_app, eT₁, eT₂]

private theorem ccAppBeta {n : Nat} (ihn : CCAt V C n) {P P' B B' W S₂ : ETrm V C} {x : V}
    (hn : elen (ETrm.comp (ETrm.app (ETrm.lam x P) B) W) ≤ n + 1)
    (hU : SNormal (ETrm.app (ETrm.lam x P) B)) (hW : SNormal W)
    (hP : PStep P P') (hB : PStep B B') (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.app (ETrm.lam x P) B) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.comp P' (ETrm.ext B' x ETrm.id)) S₂) := by
  have hAn : SNormal (ETrm.lam x P) := (snormal_app.1 hU).1
  have hBn : SNormal B := (snormal_app.1 hU).2
  have hPn : SNormal P := snormal_lam.1 hAn
  by_cases hWid : W = ETrm.id
  · subst hWid
    cases PStep.id_inv h₂
    refine ⟨ETrm.comp P' (ETrm.ext B' x ETrm.id), ?_, ?_⟩
    · rw [snf_step (SStep.idR (M := ETrm.app (ETrm.lam x P) B)), snf_of_normal hU]
      exact PStep.beta hP hB
    · exact (snf_step (SStep.idR (M := ETrm.comp P' (ETrm.ext B' x ETrm.id)))).symm
  · have hmB : elen (ETrm.comp B W) ≤ n := by
      have h := elen_comp_lt_left (X := B) (U := ETrm.app (ETrm.lam x P) B) W
        (elen_lt_app_right _ _)
      omega
    have hnormLam : SNormal (ETrm.comp (ETrm.lam x P) W) := snormal_compLam hPn hW hWid
    obtain ⟨T₂, hT₂, eT₂⟩ := ihn B W B' S₂ hmB hBn hW hB h₂
    refine ⟨ETrm.comp P' (ETrm.ext T₂ x S₂), ?_, ?_⟩
    · rw [snf_step (SStep.dApp (M := ETrm.lam x P) (N := B) (L := W)), snf_app,
        snf_of_normal hnormLam]
      exact PStep.betaClos hP h₂ hT₂
    · rw [snfClosTarget]
      exact snfCompExt rfl eT₂ (snf_step (SStep.idL (M := S₂))).symm

private theorem ccAppBetaClos {n : Nat} (ihn : CCAt V C n)
    {P P' L L' B B' W S₂ : ETrm V C} {x : V}
    (hn : elen (ETrm.comp (ETrm.app (ETrm.comp (ETrm.lam x P) L) B) W) ≤ n + 1)
    (hU : SNormal (ETrm.app (ETrm.comp (ETrm.lam x P) L) B)) (hW : SNormal W)
    (hP : PStep P P') (hL : PStep L L') (hB : PStep B B') (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.app (ETrm.comp (ETrm.lam x P) L) B) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.comp P' (ETrm.ext B' x L')) S₂) := by
  have hAn : SNormal (ETrm.comp (ETrm.lam x P) L) := (snormal_app.1 hU).1
  have hBn : SNormal B := (snormal_app.1 hU).2
  have hlamn : SNormal (ETrm.lam x P) := fun t ht => hAn _ (SStep.compL ht)
  have hPn : SNormal P := snormal_lam.1 hlamn
  have hLn : SNormal L := fun t ht => hAn _ (SStep.compR ht)
  have hmB : elen (ETrm.comp B W) ≤ n := by
    have h := elen_comp_lt_left (X := B) (U := ETrm.app (ETrm.comp (ETrm.lam x P) L) B) W
      (elen_lt_app_right _ _)
    omega
  have hmL : elen (ETrm.comp L W) ≤ n := by
    have hlt : elen L < elen (ETrm.app (ETrm.comp (ETrm.lam x P) L) B) :=
      Nat.lt_trans elen_lt_comp_lam (elen_lt_app_left _ _)
    have h := elen_comp_lt_left (X := L) (U := ETrm.app (ETrm.comp (ETrm.lam x P) L) B) W hlt
    omega
  obtain ⟨T₃, hT₃, eT₃⟩ := ihn L W L' S₂ hmL hLn hW hL h₂
  obtain ⟨T₂, hT₂, eT₂⟩ := ihn B W B' S₂ hmB hBn hW hB h₂
  have hsplit : snf (ETrm.comp (ETrm.app (ETrm.comp (ETrm.lam x P) L) B) W)
      = ETrm.app (snf (ETrm.comp (ETrm.comp (ETrm.lam x P) L) W)) (snf (ETrm.comp B W)) := by
    rw [snf_step (SStep.dApp (M := ETrm.comp (ETrm.lam x P) L) (N := B) (L := W)), snf_app]
  have hassoc : snf (ETrm.comp (ETrm.comp (ETrm.lam x P) L) W)
      = snf (ETrm.comp (ETrm.lam x P) (snf (ETrm.comp L W))) := by
    rw [snf_step (SStep.assoc (M := ETrm.lam x P) (N := L) (L := W))]
    exact snf_compR _ _
  by_cases hW₀ : snf (ETrm.comp L W) = ETrm.id
  · have hT₃id : T₃ = ETrm.id := PStep.id_inv (hW₀ ▸ hT₃)
    rw [hW₀, snf_step (SStep.idR (M := ETrm.lam x P)), snf_of_normal hlamn] at hassoc
    refine ⟨ETrm.comp P' (ETrm.ext T₂ x ETrm.id), ?_, ?_⟩
    · rw [hsplit, hassoc]
      exact PStep.beta hP hT₂
    · rw [snfClosTarget]
      refine snfCompExt rfl eT₂ ?_
      rw [← eT₃, hT₃id]
  · have hnormLam : SNormal (ETrm.comp (ETrm.lam x P) (snf (ETrm.comp L W))) :=
      snormal_compLam hPn (snf_normal _) hW₀
    rw [snf_of_normal hnormLam] at hassoc
    refine ⟨ETrm.comp P' (ETrm.ext T₂ x T₃), ?_, ?_⟩
    · rw [hsplit, hassoc]
      exact PStep.betaClos hP hT₃ hT₂
    · rw [snfClosTarget]
      exact snfCompExt rfl eT₂ eT₃

private theorem ccAppCompEps {n : Nat} (ihn : CCAt V C n) {P P' B B' W S₂ : ETrm V C}
    (hn : elen (ETrm.comp (ETrm.app (ETrm.eps P) B) W) ≤ n + 1)
    (hU : SNormal (ETrm.app (ETrm.eps P) B)) (hW : SNormal W)
    (hP : PStep P P') (hB : PStep B B') (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.app (ETrm.eps P) B) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.comp P' B') S₂) := by
  have hAn : SNormal (ETrm.eps P) := (snormal_app.1 hU).1
  have hBn : SNormal B := (snormal_app.1 hU).2
  have hmB : elen (ETrm.comp B W) ≤ n := by
    have h := elen_comp_lt_left (X := B) (U := ETrm.app (ETrm.eps P) B) W
      (elen_lt_app_right _ _)
    omega
  obtain ⟨T₂, hT₂, eT₂⟩ := ihn B W B' S₂ hmB hBn hW hB h₂
  refine ⟨ETrm.comp P' T₂, ?_, ?_⟩
  · rw [snf_step (SStep.dApp (M := ETrm.eps P) (N := B) (L := W)), snf_app,
      snf_step (SStep.epsEps (M := P) (N := W)), snf_of_normal hAn]
    exact PStep.compEps hP hT₂
  · rw [snf_step (SStep.assoc (M := P') (N := B') (L := S₂))]
    exact snfComp rfl eT₂

private theorem ccCompLam {n : Nat} (ihn : CCAt V C n) {P P' L L₁ W S₂ : ETrm V C} {x : V}
    (hn : elen (ETrm.comp (ETrm.comp (ETrm.lam x P) L) W) ≤ n + 1)
    (hU : SNormal (ETrm.comp (ETrm.lam x P) L)) (hW : SNormal W)
    (hP : PStep P P') (hL : PStep L L₁) (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.comp (ETrm.lam x P) L) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.comp (ETrm.lam x P') L₁) S₂) := by
  have hlamn : SNormal (ETrm.lam x P) := fun t ht => hU _ (SStep.compL ht)
  have hPn : SNormal P := snormal_lam.1 hlamn
  have hLn : SNormal L := fun t ht => hU _ (SStep.compR ht)
  have hmL : elen (ETrm.comp L W) ≤ n := by
    have h := elen_comp_lt_left (X := L) (U := ETrm.comp (ETrm.lam x P) L) W elen_lt_comp_lam
    omega
  obtain ⟨T₃, hT₃, eT₃⟩ := ihn L W L₁ S₂ hmL hLn hW hL h₂
  have hassoc : snf (ETrm.comp (ETrm.comp (ETrm.lam x P) L) W)
      = snf (ETrm.comp (ETrm.lam x P) (snf (ETrm.comp L W))) := by
    rw [snf_step (SStep.assoc (M := ETrm.lam x P) (N := L) (L := W))]
    exact snf_compR _ _
  have htarget : snf (ETrm.comp (ETrm.comp (ETrm.lam x P') L₁) S₂)
      = snf (ETrm.comp (ETrm.lam x P') (snf (ETrm.comp L₁ S₂))) := by
    rw [snf_step (SStep.assoc (M := ETrm.lam x P') (N := L₁) (L := S₂))]
    exact snf_compR _ _
  by_cases hW₀ : snf (ETrm.comp L W) = ETrm.id
  · have hT₃id : T₃ = ETrm.id := PStep.id_inv (hW₀ ▸ hT₃)
    rw [hW₀, snf_step (SStep.idR (M := ETrm.lam x P)), snf_of_normal hlamn] at hassoc
    refine ⟨ETrm.lam x P', ?_, ?_⟩
    · rw [hassoc]; exact PStep.lam hP
    · rw [htarget, ← eT₃, hT₃id, snf_id, snf_step (SStep.idR (M := ETrm.lam x P'))]
  · have hnormLam : SNormal (ETrm.comp (ETrm.lam x P) (snf (ETrm.comp L W))) :=
      snormal_compLam hPn (snf_normal _) hW₀
    rw [snf_of_normal hnormLam] at hassoc
    refine ⟨ETrm.comp (ETrm.lam x P') T₃, ?_, ?_⟩
    · rw [hassoc]; exact PStep.comp (PStep.lam hP) hT₃
    · rw [htarget]
      refine snfComp rfl ?_
      rw [snf_idem]; exact eT₃

private theorem ccCompVar {n : Nat} (ihn : CCAt V C n) {L L₁ W S₂ : ETrm V C} {y : V}
    (hn : elen (ETrm.comp (ETrm.comp (ETrm.var y) L) W) ≤ n + 1)
    (hU : SNormal (ETrm.comp (ETrm.var y) L)) (hW : SNormal W)
    (hL : PStep L L₁) (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp (ETrm.comp (ETrm.var y) L) W)) S ∧
      snf S = snf (ETrm.comp (ETrm.comp (ETrm.var y) L₁) S₂) := by
  have hLn : SNormal L := fun t ht => hU _ (SStep.compR ht)
  have hmL : elen (ETrm.comp L W) ≤ n := by
    have h := elen_comp_lt_left (X := L) (U := ETrm.comp (ETrm.var y) L) W elen_lt_comp_var
    omega
  obtain ⟨T₃, hT₃, eT₃⟩ := ihn L W L₁ S₂ hmL hLn hW hL h₂
  have hm2 : elen (ETrm.comp (ETrm.var y) (snf (ETrm.comp L W))) ≤ n := by
    have h := elen_var_snf_lt (x := y) L W
    omega
  obtain ⟨S, hS, eS⟩ := ihn (ETrm.var y) (snf (ETrm.comp L W)) (ETrm.var y) T₃ hm2
    (snormal_var y) (snf_normal _) PStep.refl hT₃
  have hassoc : snf (ETrm.comp (ETrm.comp (ETrm.var y) L) W)
      = snf (ETrm.comp (ETrm.var y) (snf (ETrm.comp L W))) := by
    rw [snf_step (SStep.assoc (M := ETrm.var y) (N := L) (L := W))]
    exact snf_compR _ _
  refine ⟨S, ?_, ?_⟩
  · rw [hassoc]; exact hS
  · rw [eS, snf_step (SStep.assoc (M := ETrm.var y) (N := L₁) (L := S₂))]
    exact snfComp rfl eT₃

private theorem ccVarExt {n : Nat} (ihn : CCAt V C n) {P P' Q Q' : ETrm V C} {x y : V}
    (hn : elen (ETrm.comp (ETrm.var x) (ETrm.ext P y Q)) ≤ n + 1)
    (hW : SNormal (ETrm.ext P y Q)) (hxy : y ≠ x)
    (_hP : PStep P P') (hQ : PStep Q Q') :
    ∃ S, PStep (snf (ETrm.comp (ETrm.var x) (ETrm.ext P y Q))) S ∧
      snf S = snf (ETrm.comp (ETrm.var x) (ETrm.ext P' y Q')) := by
  have hQn : SNormal Q := (snormal_ext.1 hW).2
  have hm : elen (ETrm.comp (ETrm.var x) Q) ≤ n := by
    have h : elen (ETrm.comp (ETrm.var (C := C) x) Q)
        < elen (ETrm.comp (ETrm.var x) (ETrm.ext P y Q)) := by
      simp only [elen]; have := elen_pos P; omega
    omega
  obtain ⟨S, hS, eS⟩ := ihn (ETrm.var x) Q (ETrm.var x) Q' hm (snormal_var x) hQn PStep.refl hQ
  refine ⟨S, ?_, ?_⟩
  · rw [snf_step (SStep.varSkip (M := P) (N := Q) hxy)]; exact hS
  · rw [eS, snf_step (SStep.varSkip (M := P') (N := Q') hxy)]

/-! ## The induction -/

private theorem ccBounded : ∀ (n : Nat), CCAt V C n := by
  intro n
  induction n with
  | zero =>
      intro U W S₁ S₂ hn _ _ _ _
      have := elen_pos (ETrm.comp U W)
      omega
  | succ n ihn =>
      intro U W S₁ S₂ hn hU hW h₁ h₂
      cases U with
      | id =>
          cases PStep.id_inv h₁
          refine ⟨S₂, ?_, ?_⟩
          · rw [snf_step (SStep.idL (M := W)), snf_of_normal hW]
            exact h₂
          · rw [snf_step (SStep.idL (M := S₂))]
      | const c =>
          cases PStep.const_inv h₁
          refine ⟨ETrm.const c, ?_, ?_⟩
          · rw [snf_step (SStep.constC (c := c) (N := W)), snf_const]
            exact PStep.refl
          · rw [snf_step (SStep.constC (c := c) (N := S₂))]
      | eps A =>
          obtain ⟨A', rfl, hA'⟩ := PStep.eps_inv h₁
          refine ⟨ETrm.eps A', ?_, ?_⟩
          · rw [snf_step (SStep.epsEps (M := A) (N := W)), snf_of_normal hU]
            exact PStep.eps hA'
          · rw [snf_step (SStep.epsEps (M := A') (N := S₂))]
      | lam x A =>
          have hA : SNormal A := snormal_lam.1 hU
          obtain ⟨A', rfl, hA'⟩ := PStep.lam_inv h₁
          by_cases hWid : W = ETrm.id
          · subst hWid
            cases PStep.id_inv h₂
            refine ⟨ETrm.lam x A', ?_, ?_⟩
            · rw [snf_step (SStep.idR (M := ETrm.lam x A)), snf_of_normal hU]
              exact PStep.lam hA'
            · rw [snf_step (SStep.idR (M := ETrm.lam x A'))]
          · have hnorm : SNormal (ETrm.comp (ETrm.lam x A) W) := snormal_compLam hA hW hWid
            refine ⟨ETrm.comp (ETrm.lam x A') S₂, ?_, ?_⟩
            · rw [snf_of_normal hnorm]
              exact PStep.comp (PStep.lam hA') h₂
            · rfl
      | var x =>
          cases PStep.var_inv h₁
          by_cases hWid : W = ETrm.id
          · subst hWid
            cases PStep.id_inv h₂
            refine ⟨ETrm.var x, ?_, ?_⟩
            · rw [snf_step (SStep.idR (M := (ETrm.var x : ETrm V C))), snf_var]
              exact PStep.refl
            · rw [snf_step (SStep.idR (M := (ETrm.var x : ETrm V C)))]
          · by_cases hWext : ∃ (P : ETrm V C) (y : V) (Q : ETrm V C), W = ETrm.ext P y Q
            · obtain ⟨P, y, Q, rfl⟩ := hWext
              obtain ⟨P', Q', rfl, hP', hQ'⟩ := PStep.ext_inv h₂
              by_cases hxy : y = x
              · subst hxy
                have hPn : SNormal P := (snormal_ext.1 hW).1
                refine ⟨P', ?_, ?_⟩
                · rw [snf_step (SStep.varRef (x := y) (M := P) (N := Q)), snf_of_normal hPn]
                  exact hP'
                · rw [snf_step (SStep.varRef (x := y) (M := P') (N := Q'))]
              · exact ccVarExt ihn hn hW hxy hP' hQ'
            · have hnorm : SNormal (ETrm.comp (ETrm.var x) W) :=
                snormal_compVar hW hWid (fun P y Q h => hWext ⟨P, y, Q, h⟩)
              refine ⟨ETrm.comp (ETrm.var x) S₂, ?_, ?_⟩
              · rw [snf_of_normal hnorm]
                exact PStep.comp PStep.refl h₂
              · rfl
      | ext A x B =>
          have hAn : SNormal A := (snormal_ext.1 hU).1
          have hBn : SNormal B := (snormal_ext.1 hU).2
          obtain ⟨A', B', rfl, hA', hB'⟩ := PStep.ext_inv h₁
          have hmA : elen (ETrm.comp A W) ≤ n := by
            have h := elen_comp_lt_left (X := A) (U := ETrm.ext A x B) W
              (elen_lt_ext_left A x B)
            omega
          have hmB : elen (ETrm.comp B W) ≤ n := by
            have h := elen_comp_lt_left (X := B) (U := ETrm.ext A x B) W
              (elen_lt_ext_right A x B)
            omega
          obtain ⟨T₁, hT₁, eT₁⟩ := ihn A W A' S₂ hmA hAn hW hA' h₂
          obtain ⟨T₂, hT₂, eT₂⟩ := ihn B W B' S₂ hmB hBn hW hB' h₂
          refine ⟨ETrm.ext T₁ x T₂, ?_, ?_⟩
          · rw [snf_step (SStep.dExt (L := A) (x := x) (M := B) (N := W)), snf_ext]
            exact PStep.ext hT₁ hT₂
          · rw [snf_ext, snf_step (SStep.dExt (L := A') (x := x) (M := B') (N := S₂)),
              snf_ext, eT₁, eT₂]
      | app A B =>
          have hAn : SNormal A := (snormal_app.1 hU).1
          have hBn : SNormal B := (snormal_app.1 hU).2
          cases h₁ with
          | refl => exact ccApp ihn hn hAn hBn hW PStep.refl PStep.refl h₂
          | app hA' hB' => exact ccApp ihn hn hAn hBn hW hA' hB' h₂
          | beta hP hB' => exact ccAppBeta ihn hn hU hW hP hB' h₂
          | betaClos hP hL hB' => exact ccAppBetaClos ihn hn hU hW hP hL hB' h₂
          | compEps hP hB' => exact ccAppCompEps ihn hn hU hW hP hB' h₂
      | comp A L =>
          obtain ⟨A₁, L₁, rfl, hA₁, hL₁⟩ := PStep.comp_inv h₁
          cases A with
          | lam x P =>
              obtain ⟨P', rfl, hP⟩ := PStep.lam_inv hA₁
              exact ccCompLam ihn hn hU hW hP hL₁ h₂
          | var y =>
              cases PStep.var_inv hA₁
              exact ccCompVar ihn hn hU hW hL₁ h₂
          | id => exact (hU _ SStep.idL).elim
          | const c => exact (hU _ SStep.constC).elim
          | app _ _ => exact (hU _ SStep.dApp).elim
          | ext _ _ _ => exact (hU _ SStep.dExt).elim
          | eps _ => exact (hU _ SStep.epsEps).elim
          | comp _ _ => exact (hU _ SStep.assoc).elim

/-- **Composition compatibility.** -/
theorem cc {U W S₁ S₂ : ETrm V C} (hU : SNormal U) (hW : SNormal W)
    (h₁ : PStep U S₁) (h₂ : PStep W S₂) :
    ∃ S, PStep (snf (ETrm.comp U W)) S ∧ snf S = snf (ETrm.comp S₁ S₂) :=
  ccBounded _ U W S₁ S₂ (Nat.le_refl _) hU hW h₁ h₂

end EnvEps

end LambdaFrenv
