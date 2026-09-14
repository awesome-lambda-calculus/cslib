/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/

module

public import Cslib.Foundations.Relation.Attr
public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.Relation.Confluence


/-!
# Abstract postponement lemma

r₁ purely relational lemma: if a single `r₂`-step followed by a single `r₁`-step
can be reorganized into a single `r₁`-step followed by a (reflexive-transitive)
sequence of `r₂`-steps, then in any mixed `r₁`/`r₂` reduction sequence all the
`r₂`-steps can be postponed to the end.

This is the abstract heart of η-postponement, instantiated later with
`r₁ := parallel β-reduction` and `r₂ := η-reduction`.
-/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

variable {α : Type*} {r₁ r₂ : α → α → Prop}

def WeakPostpone (r₁ r₂ : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r₂ y x → r₁ y z →
    ∃ w, TransGen r₁ x w ∧ ReflTransGen r₂ z w

def WeakPlusPostpone (r₁ r₂ : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r₂ y x → Relation.TransGen r₁ y z →
    ∃ w, Relation.TransGen r₁ x w ∧ ReflTransGen r₂ z w


theorem single_over_plus
  (hW : DiamondCommute (Relation.ReflTransGen r₁) (Relation.ReflTransGen r₂))
  (hL : WeakPostpone r₁ r₂) :
  WeakPlusPostpone r₁ r₂ := by
  intros x y z hxy hyz
  induction hyz with
  | single hyz => exact hL hxy hyz
  | tail h₁ h₂ h₃ =>
    obtain ⟨w, hw₁, hw₂⟩ := h₃
    exact Exists.elim (hW (.single h₂) hw₂) fun s hs => ⟨s, hw₁.trans_left hs.2, hs.1⟩

theorem star_over_plus
  (hW : DiamondCommute (Relation.ReflTransGen r₁) (Relation.ReflTransGen r₂))
  (hL : WeakPostpone r₁ r₂) :
  DiamondCommute (Relation.TransGen r₁) (Relation.ReflTransGen r₂) := by
  have hP : WeakPlusPostpone r₁ r₂ := single_over_plus hW hL
  intro q p r hB hA
  induction hA generalizing p with
  | refl => exact ⟨p, .refl, hB⟩
  | tail _ b_step ih =>
    obtain ⟨s, hs₁, hs₂⟩ := ih hB
    obtain ⟨w, hw₁, hw₂⟩ := hP b_step hs₂
    exact ⟨w, hs₁.trans hw₂, hw₁⟩

/-
--  DiamondCommute.diamond_commute_reflTransGen_left
theorem postpone_a (h : DiamondCommute r₂ r₁) :
   DiamondCommute r₂ (Relation.ReflTransGen r₁) := by
  intro q p r hB hA
  induction hA generalizing p with
  | refl => exact ⟨p, .refl, hB⟩
  | tail _ a_step ih =>
    obtain ⟨s, hs₁, hs₂⟩ := ih hB
    obtain ⟨w, hw₁, hw₂⟩ := h hs₂ a_step
    exact ⟨w, hs₁.tail hw₁, hw₂⟩

-- unused
theorem postpone_b (h : DiamondCommute r₂ r₁) :
   DiamondCommute (Relation.ReflTransGen r₂) r₁ := by
  intro q p r hB hA
  induction hB generalizing r with
  | refl => exact ⟨r, hA, .refl⟩
  | tail _ b_step ih =>
    obtain ⟨s, hs₁, hs₂⟩ := ih hA
    obtain ⟨w, hw₁, hw₂⟩ := h b_step hs₁
    exact ⟨w, hw₁, hs₂.tail hw₂⟩
-/

theorem postpone_ab (h : DiamondCommute r₂ r₁) :
   DiamondCommute (Relation.ReflTransGen r₂) (Relation.ReflTransGen r₁) :=
   DiamondCommute.to_commute h

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
