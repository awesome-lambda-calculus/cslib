/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/

module

public import Cslib.Foundations.Relation.Attr


/-!
# Abstract postponement lemma

A purely relational lemma: if a single `B`-step followed by a single `A`-step
can be reorganized into a single `A`-step followed by a (reflexive-transitive)
sequence of `B`-steps, then in any mixed `A`/`B` reduction sequence all the
`B`-steps can be postponed to the end.

This is the abstract heart of η-postponement, instantiated later with
`A := parallel β-reduction` and `B := η-reduction`.
-/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {α : Type*} {A B : α → α → Prop}

/-- Weak commutation: a `B`-star followed by an `A`-star can be reorganized into
an `A`-star followed by a `B`-star. -/
def WeakCommute (A B : α → α → Prop) : Prop :=
  ∀ ⦃p q r⦄, Relation.ReflTransGen B p q → Relation.ReflTransGen A q r
      → ∃ s, Relation.ReflTransGen A p s ∧ Relation.ReflTransGen B s r

/-- Strong local postponement: a single `B`-step followed by a single `A`-step
reorganizes into a *non-empty* sequence of `A`-steps followed by a `B`-star. -/
def StrongLocal (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → A y z → ∃ w, Relation.TransGen A x w ∧ Relation.ReflTransGen B w z

/-- Local postponement hypothesis: `B` followed by a single `A` reorganizes into
a single `A` followed by a sequence of `B`s. -/
def LocalPostpone (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → A y z → ∃ q, A x q ∧ Relation.ReflTransGen B q z

/-
A sequence of `B`-steps followed by a single `A`-step reorganizes into a
sequence of `A`-steps followed by a sequence of `B`-steps.
-/
theorem swap_star_single (h : LocalPostpone A B) {p q r : α}
    (hpq : Relation.ReflTransGen B p q) (hqr : A q r) :
    ∃ w, Relation.ReflTransGen A p w ∧ Relation.ReflTransGen B w r := by
      revert hpq hqr
      intro hpq hqr
      induction hpq generalizing r with
      | refl => exact ⟨ r, .single hqr, .refl ⟩
      | tail _ ih h' =>
        obtain ⟨ w, hw₁, hw₂ ⟩ := h ih hqr
        exact h' hw₁ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂.trans hw₂ ⟩

/-
**Abstract postponement.** In any mixed reduction sequence, all `B`-steps can
be postponed past all `A`-steps.
-/
theorem postpone (h : LocalPostpone A B) {x y : α}
    (hxy : Relation.ReflTransGen (fun a b => A a b ∨ B a b) x y) :
    ∃ w, Relation.ReflTransGen A x w ∧ Relation.ReflTransGen B w y := by
      induction hxy with
      | refl => exact ⟨ x, by rfl, by rfl ⟩
      | tail _ ih _ =>
        obtain ⟨ w, hw₁, hw₂ ⟩ := ‹_›
        rcases ih with ( ih | ih )
        · obtain ⟨ q, hq₁, hq₂ ⟩ := swap_star_single h hw₂ ih
          exact ⟨ q, hw₁.trans hq₁, hq₂ ⟩
        · exact ⟨ w, hw₁, hw₂.tail ih ⟩

/-
A single `B`-step followed by a non-empty `A`-sequence reorganizes into a
non-empty `A`-sequence followed by a `B`-star.
-/
theorem single_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {x y z : α} (hxy : B x y) (hyz : Relation.TransGen A y z) :
    ∃ (w : α), Relation.TransGen A x w ∧ Relation.ReflTransGen B w z := by
  induction hyz with
  | single hyz => exact hL hxy hyz
  | tail h₁ h₂ h₃ =>
    obtain ⟨ w, hw₁, hw₂ ⟩ := h₃
    exact Exists.elim (hW hw₂ (.single h₂)) fun s hs => ⟨s, hw₁.trans_left hs.1, hs.2⟩

/-
A `B`-star followed by a non-empty `A`-sequence reorganizes into a non-empty
`A`-sequence followed by a `B`-star.
-/
theorem star_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {a b c : α} (hab : Relation.ReflTransGen B a b) (hbc : Relation.TransGen A b c) :
    ∃ w, Relation.TransGen A a w ∧ Relation.ReflTransGen B w c := by
  induction hab generalizing c with
  | refl => exact ⟨ c, hbc, by rfl ⟩
  | tail _ hB hA =>
    exact single_over_plus hW hL hB hbc |> fun ⟨ w, hw₁, hw₂ ⟩ => hA hw₁ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂.trans hw₂ ⟩


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
