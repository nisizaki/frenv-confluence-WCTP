import LambdaFrenv.Basic

/-!
# Abstract rewriting theory

Generic facts about an abstract relation `r : α → α → Prop` and its
reflexive-transitive closure `ReflTransGen r`, used by the confluence
proof.  Lean's core library ships no abstract-rewriting theory and this
development deliberately avoids Mathlib, so everything is proved here:

* closure combinators (`head`, `mono`, `lift`, `casesHead`),
* the diamond property and `Diamond.confluent`,
* transfer of confluence along `r ⊆ s ⊆ r*` (`confluent_of_between`),
* strong normalization `SN` and Newman's lemma (`newman`).
-/

namespace LambdaFrenv

universe u

variable {α : Type u} {r s : α → α → Prop}

namespace ReflTransGen

/-- Prepend a single step to a multi-step reduction. -/
theorem head {a b c : α} (h₁ : r a b) (h₂ : ReflTransGen r b c) : ReflTransGen r a c :=
  ReflTransGen.trans (ReflTransGen.single h₁) h₂

/-- Monotonicity of the closure in the relation. -/
theorem mono {a b : α} (h : ∀ x y, r x y → s x y) (hab : ReflTransGen r a b) :
    ReflTransGen s a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (h _ _ hstep)

/-- If every `r`-step is an `s`-multi-step then every `r`-multi-step is one. -/
theorem lift {a b : α} (h : ∀ x y, r x y → ReflTransGen s x y) (hab : ReflTransGen r a b) :
    ReflTransGen s a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.trans ih (h _ _ hstep)

/-- Decomposition at the head of a multi-step reduction. -/
theorem casesHead {a b : α} (h : ReflTransGen r a b) :
    a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      rcases ih with rfl | ⟨d, had, hdb⟩
      · exact Or.inr ⟨_, hstep, ReflTransGen.refl⟩
      · exact Or.inr ⟨d, had, ReflTransGen.tail hdb hstep⟩

/-- Transport a multi-step reduction along a congruence. -/
theorem map {β : Type u} {s : β → β → Prop} (f : α → β)
    (hf : ∀ x y, r x y → s (f x) (f y)) {a b : α} (h : ReflTransGen r a b) :
    ReflTransGen s (f a) (f b) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ReflTransGen.tail ih (hf _ _ hstep)

end ReflTransGen

/-! ## Diamond property -/

/-- The diamond property: two single steps from a common source are joined
by a single step on each side. -/
def Diamond (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c : α⦄, r a b → r a c → ∃ d, r b d ∧ r c d

namespace Diamond

/-- Strip lemma: one step against a multi-step. -/
theorem strip (hd : Diamond r) {a b c : α} (hab : r a b) (hac : ReflTransGen r a c) :
    ∃ d, ReflTransGen r b d ∧ r c d := by
  induction hac with
  | refl => exact ⟨b, ReflTransGen.refl, hab⟩
  | tail _ hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih
      obtain ⟨e, hde, hce⟩ := hd hcd hstep
      exact ⟨e, ReflTransGen.tail hbd hde, hce⟩

/-- A relation with the diamond property is confluent. -/
theorem confluent (hd : Diamond r) : Confluent r := by
  intro a b c hab hac
  induction hab with
  | refl => exact ⟨c, hac, ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih
      obtain ⟨e, hbe, hde⟩ := hd.strip hstep hbd
      exact ⟨e, hbe, ReflTransGen.tail hcd hde⟩

end Diamond

/-- If `r ⊆ s` and `s ⊆ r*`, confluence of `s` gives confluence of `r`. -/
theorem confluent_of_between (h₁ : ∀ x y, r x y → s x y)
    (h₂ : ∀ x y, s x y → ReflTransGen r x y) (hs : Confluent s) : Confluent r := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hs (ReflTransGen.mono h₁ hab) (ReflTransGen.mono h₁ hac)
  exact ⟨d, ReflTransGen.lift h₂ hbd, ReflTransGen.lift h₂ hcd⟩

/-! ## Newman's lemma -/

/-- Local (weak) confluence. -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c : α⦄, r a b → r a c → ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d

/-- Strong normalization: every element is accessible for the reversed relation,
i.e. there is no infinite `r`-reduction. -/
def SN (r : α → α → Prop) : Prop :=
  ∀ a : α, Acc (fun x y => r y x) a

/-- Newman's lemma: a strongly normalizing, locally confluent relation is
confluent. -/
theorem newman (hsn : SN r) (hlc : LocallyConfluent r) : Confluent r := by
  have key : ∀ a : α, Acc (fun x y => r y x) a →
      ∀ b c : α, ReflTransGen r a b → ReflTransGen r a c →
        ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d := by
    intro a ha
    induction ha with
    | intro a _ ih =>
        intro b c hab hac
        rcases ReflTransGen.casesHead hab with rfl | ⟨b₁, hab₁, hb₁b⟩
        · exact ⟨c, hac, ReflTransGen.refl⟩
        rcases ReflTransGen.casesHead hac with rfl | ⟨c₁, hac₁, hc₁c⟩
        · exact ⟨b, ReflTransGen.refl, hab⟩
        obtain ⟨d, hb₁d, hc₁d⟩ := hlc hab₁ hac₁
        obtain ⟨e, hbe, hde⟩ := ih b₁ hab₁ b d hb₁b hb₁d
        obtain ⟨f, hcf, hef⟩ := ih c₁ hac₁ c e hc₁c (ReflTransGen.trans hc₁d hde)
        exact ⟨f, ReflTransGen.trans hbe hef, hcf⟩
  intro a b c hab hac
  exact key a (hsn a) b c hab hac

/-- Strong normalization transported along a measure into `Nat`. -/
theorem SN.ofMeasure {r : α → α → Prop} (m : α → Nat)
    (h : ∀ x y, r x y → m y < m x) : SN r := by
  have hwf : WellFounded (fun x y : α => m x < m y) := InvImage.wf m Nat.lt_wfRel.wf
  intro a
  have hacc := hwf.apply a
  induction hacc with
  | intro x _ ih => exact Acc.intro x (fun y hy => ih y (h x y hy))

end LambdaFrenv
