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
      revert hpq hqr;
      intro hpq hqr
      induction hpq generalizing r with
      | refl => exact ⟨ r, .single hqr, .refl ⟩;
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
      | refl => exact ⟨ x, by rfl, by rfl ⟩;
      | tail _ ih _ =>
        obtain ⟨ w, hw₁, hw₂ ⟩ := ‹_›;
        rcases ih with ( ih | ih );
        · obtain ⟨ q, hq₁, hq₂ ⟩ := swap_star_single h hw₂ ih;
          exact ⟨ q, hw₁.trans hq₁, hq₂ ⟩;
        · exact ⟨ w, hw₁, hw₂.tail ih ⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
