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

@[grind]
def LocalPostpone (A B : α → α → Prop) : Prop :=
  ∀ ⦃p q r⦄, B p q → A q r → ∃ s, A p s ∧ B s r

/-- Strong local postponement: a single `B`-step followed by a single `A`-step
reorganizes into a *non-empty* sequence of `A`-steps followed by a `B`-star. -/
def WeakPostpone (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → A y z →
    ∃ w, Relation.TransGen A x w ∧ Relation.ReflTransGen B w z

def WeakWeakPostpone (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → Relation.TransGen A y z →
    ∃ w, Relation.TransGen A x w ∧ Relation.ReflTransGen B w z


/-
A single `B`-step followed by a non-empty `A`-sequence reorganizes into a
non-empty `A`-sequence followed by a `B`-star.
-/
theorem single_over_plus
  (hW : LocalPostpone (Relation.ReflTransGen A) (Relation.ReflTransGen B))
  (hL : WeakPostpone A B) :
  WeakWeakPostpone A B := by
  intros x y z hxy hyz
  induction hyz with
  | single hyz => exact hL hxy hyz
  | tail h₁ h₂ h₃ =>
    obtain ⟨ w, hw₁, hw₂ ⟩ := h₃
    exact Exists.elim (hW hw₂ (.single h₂)) fun s hs => ⟨s, hw₁.trans_left hs.1, hs.2⟩

/-
A `B`-star followed by a non-empty `A`-sequence reorganizes into a non-empty
`A`-sequence followed by a `B`-star.
-/
theorem star_over_plus
  (hW : LocalPostpone (Relation.ReflTransGen A) (Relation.ReflTransGen B))
  (hL : WeakPostpone A B) :
  LocalPostpone (Relation.TransGen A) (Relation.ReflTransGen B) := by
  intros a b c hab hbc
  induction hab generalizing c with
  | refl => exact ⟨ c, hbc, by rfl ⟩
  | tail _ hB hA =>
    exact single_over_plus hW hL hB hbc |> fun ⟨ w, hw₁, hw₂ ⟩ => hA hw₁ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂.trans hw₂ ⟩

theorem postpone_a (h : LocalPostpone A B) :
   LocalPostpone (Relation.ReflTransGen A) B := by
  intros p q r hB hA
  induction hA generalizing p with grind

theorem postpone_b (h : LocalPostpone A B) :
   LocalPostpone A (Relation.ReflTransGen B) := by
  intros p q r hB hA
  induction hB generalizing r with grind

theorem postpone_ab (h : LocalPostpone A B) :
   LocalPostpone (Relation.ReflTransGen A) (Relation.ReflTransGen B) := by
  intros p q r hB hA
  induction hB generalizing r with
  | refl => grind
  | tail _ b_step ih =>
    -- 1. Push the final single B step past the A* steps
    have ⟨s', hA_s', hB_s'⟩ := postpone_a h b_step hA
    -- 2. Use the induction hypothesis to push the rest of the B* steps past the new A* steps
    have ⟨s'', hA_s'', hB_s''⟩ := ih hA_s'
    -- 3. Combine the results to form the full A* and B* paths
    exact ⟨s'', hA_s'', Relation.ReflTransGen.tail hB_s'' hB_s'⟩


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
