/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez, Yijun Leng
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEtaConfluence

/-! # βη-Confluence for the λ-calculus

## Reference

* [T. Nipkow, *More Church-Rosser Proofs (in Isabelle/HOL)*][Nipkow2001]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- Full βη-reduction. -/
@[reduction_sys "βηᶠ"]
abbrev FullBetaEta : Term Var → Term Var → Prop := FullBeta ⊔ FullEta

namespace FullBetaEta

variable {M M' N N' : Term Var}

theorem step_app_l_cong (step : M ⭢βηᶠ M') (lc_N : LC N) : app M N ⭢βηᶠ app M' N := by
    rcases step with h | h
    · exact join_inl (h.appR lc_N)
    · exact join_inr (h.appR lc_N)

theorem step_app_r_cong (step : M ⭢βηᶠ M') (lc_N : LC N) : app N M ⭢βηᶠ app N M' := by
    rcases step with h | h
    · exact join_inl (h.appL lc_N)
    · exact join_inr (h.appL lc_N)

theorem steps_app_l_cong (steps : M ↠βηᶠ M') (lc_N : LC N) : app M N ↠βηᶠ app M' N := by
  induction steps with
  | refl => grind
  | tail _ h ih => exact ih.tail (step_app_l_cong h lc_N)

theorem steps_app_r_cong (steps : M ↠βηᶠ M') (lc_N : LC N) : app N M ↠βηᶠ app N M' := by
  induction steps with
  | refl => grind
  | tail _ h ih => exact ih.tail (step_app_r_cong h lc_N)

theorem normal_fullbeta_iff :
  Relation.Normal FullBetaEta M ↔ Relation.Normal FullBeta M /\ Relation.Normal FullEta M := by
  constructor
  · intros hbetaeta
    constructor <;> intros h <;> apply hbetaeta <;> obtain ⟨t, _⟩ := h <;> exists t <;> grind
  · intros h
    obtain ⟨hbeta, heta⟩ := h
    intros h
    obtain ⟨t, h⟩ := h
    cases h <;> grind

variable [HasFresh Var] [DecidableEq Var]

lemma step_fv (step : M ⭢βηᶠ N) : N.fv ⊆ M.fv := by
    cases step with
    | inl h => grind [FullBeta.step_not_fv h]
    | inr h => grind [FullEta.step_not_fv h]

lemma steps_fv (steps : M ↠βηᶠ N) : N.fv ⊆ M.fv := by
  induction steps with
  | refl => grind
  | tail _ step _ => grind [step_fv step]

lemma step_subst_cong_l (s s' t : Term Var) (x : Var) (step : s ⭢βηᶠ s') (h_lc : LC t) :
    s[x := t] ⭢βηᶠ s'[x := t] := by
  cases step with
  | inl h => left
             apply FullBeta.redex_subst_cong_lc _ _ _ _ h h_lc
  | inr h =>  right
              apply FullEta.step_subst_cong_l _ _ _  h h_lc

lemma steps_subst_cong_l (s s' t : Term Var) (x : Var) (steps : s ↠βηᶠ s') (h_lc : LC t) :
    s[x := t] ↠βηᶠ s'[x := t] := by
  induction steps with grind [step_subst_cong_l]

end FullBetaEta

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
