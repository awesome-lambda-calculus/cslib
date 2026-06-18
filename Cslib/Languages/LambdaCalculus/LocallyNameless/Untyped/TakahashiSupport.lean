/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

-- public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaCongr

/-!
# Support lemmas for Takahashi's η/β commutation lemma

A size measure (with opening invariance), a generalized open/close identity, the
"η in body position" lemma, and the two witness-packaging lemmas that handle the
cofinite-quantification uniformity via closing.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} [Infinite Var] [DecidableEq Var]

/-
η-reduction in body position: a cofinite family of body reductions yields a
reduction of the openings by a fixed locally closed term.
-/
theorem open_body {C D : Term Var} (xs : Finset Var)
    (h : ∀ x ∉ xs, (C ^ fvar x) ↠ηᶠ (D ^ fvar x)) {u : Term Var} (hu : LC u) :
    (C ^ u) ↠ηᶠ (D ^ u) := by
  obtain ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  have hz_fv_C : z ∉ Term.fv C := by grind
  have hz_fv_D : z ∉ Term.fv D := by grind
  rw [Term.subst_intro _ _ _ hz_fv_C, Term.subst_intro _ _ _ hz_fv_D]
  exact FullEta.steps_subst_cong_l _ _ _ (h z (by grind)) hu

/-
Witness packaging for the abstraction case.
-/
theorem exists_Q_abs {M0 P0 W : Term Var} (z : Var)
    (hz0 : z ∉ fv M0) (hzP : z ∉ fv P0)
    (hpar : Parallel (M0 ^ fvar z) W) (heta : W ↠ηᶠ (P0 ^ fvar z)) :
    ∃ Q, Parallel (Term.abs M0) Q ∧ Q ↠ηᶠ (Term.abs P0) := by
  exists Term.abs ( closeRec 0 z W )
  constructor
  · apply Parallel.abs ({ z } ∪ M0.fv ∪ W.fv)
    intro x hx
    convert para_subst z hpar ( Parallel.fvar x ) <;> grind
  · have h_subst : ∀ x, x ∉ {z} ∪ W.fv ∪ P0.fv → Term.subst W z (fvar x) ↠ηᶠ Term.subst (P0 ^ fvar z) z (fvar x) := by
      exact fun x hx => FullEta.steps_subst_cong_l _ _ _ heta (LC.fvar x)
    apply FullEta.redex_abs_cong
    · intro x hx
      convert h_subst x hx <;> grind
    · apply LC.abs
      · intro x hx
        convert h_subst x hx
        grind

/-
Witness packaging for the β-redex-creation case.
-/
theorem exists_Q_app_abs {A M1' W Z N1' : Term Var} (z : Var)
    (hz0 : z ∉ fv A) (hzP : z ∉ fv M1')
    (hpar : Parallel (A ^ fvar z) W) (heta : W ↠ηᶠ (M1' ^ fvar z))
    (hZ : Parallel Z N1') :
    ∃ Q, Parallel (Term.app (Term.abs A) Z) Q ∧ Q ↠ηᶠ (M1' ^ N1') := by
  exists ( closeRec 0 z W ) ^ N1'
  constructor
  · convert Parallel.beta ( { z } ∪ A.fv ∪ W.fv ) _ hZ
    intro x hx
    convert para_subst z hpar ( Parallel.fvar x ) <;> grind
  · convert open_body ( { z } ∪ W.fv ∪ M1'.fv ) _ _
    · intro x hx
      convert FullEta.steps_subst_cong_l _ _ _ heta ( LC.fvar x )
      · apply close_open_to_subst <;> grind
      · rw [ subst_intro ]
        exact hzP
    · grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
