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
  | tail _ h ih =>
    refine ih.tail ?_
    rcases h with h | h
    · exact join_inl (h.appR lc_N)
    · exact join_inr (h.appR lc_N)

theorem steps_app_r_cong (steps : M ↠βηᶠ M') (lc_N : LC N) : app N M ↠βηᶠ app N M' := by
  induction steps with
  | refl => grind
  | tail _ h ih =>
    refine ih.tail ?_
    rcases h with h | h
    · exact join_inl (h.appL lc_N)
    · exact join_inr (h.appL lc_N)

lemma steps_fv [HasFresh Var] [DecidableEq Var] (steps : M ↠βηᶠ N) : N.fv ⊆ M.fv := by
  induction steps with
  | refl => grind
  | tail _ h _ => cases h with
    | inl h => grind [FullBeta.step_not_fv h]
    | inr h => grind [FullEta.step_not_fv h]

theorem from_beta (redex : M ↠βᶠ M') :  M ↠βηᶠ M' := by grind

theorem from_eta (redex : M ↠ηᶠ M') :  M ↠βηᶠ M' := by grind

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

end FullBetaEta

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
