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

r₂ purely relational lemma: if a single `r₁`-step followed by a single `r₂`-step
can be reorganized into a single `r₂`-step followed by a (reflexive-transitive)
sequence of `r₁`-steps, then in any mixed `r₂`/`r₁` reduction sequence all the
`r₁`-steps can be postponed to the end.

This is the abstract heart of η-postponement, instantiated later with
`r₂ := parallel β-reduction` and `r₁ := η-reduction`.
-/

@[expose] public section

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

variable {α : Type*}

abbrev WeakPostpone (r₁ r₂ : α → α → Prop) : Prop :=
  ∀ ⦃x y₁ y₂⦄, r₂ x y₁ → r₁ x y₂ →
    ∃ z, ReflTransGen r₁ y₁ z ∧ TransGen r₂ y₂ z

abbrev WeakPlusPostpone (r₁ r₂ : α → α → Prop) : Prop :=
  ∀ ⦃x y₁ y₂⦄, TransGen r₂ x y₁ → r₁ x y₂ →
    ∃ z, ReflTransGen r₁ y₁ z ∧ TransGen r₂ y₂ z

-- SemiCommute.to_commute
theorem star_over_plus (r₁ r₂ : α → α → Prop)
  (h : WeakPlusPostpone r₁ r₂) :
  DiamondCommute (ReflTransGen r₁) (TransGen r₂) := by
  intro q p r hB hA
  induction hB generalizing r with
  | refl => exact ⟨r, hA, .refl⟩
  | tail _ b_step ih =>
    obtain ⟨s, hs₁, hs₂⟩ := ih hA
    obtain ⟨w, hw₁, hw₂⟩ := h hs₁ b_step
    exact ⟨w, hw₂, hs₂.trans hw₁⟩

theorem single_over_plus (r₁ r₂ : α → α → Prop)
  (hW : Commute r₁ r₂)
  (hL : WeakPostpone r₁ r₂) :
  WeakPlusPostpone r₁ r₂ := by
  intros x y z hxy hyz
  induction hxy with
  | single hxy => exact hL hxy hyz
  | tail h₁ h₂ h₃ =>
    obtain ⟨w, hw₁, hw₂⟩ := h₃
    obtain ⟨s, hs₁, hs₂⟩ := hW hw₁ (.single h₂)
    exact ⟨s, hs₂, hw₂.trans_left hs₁⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
