/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract

/-!
# Takahashi's η/β commutation lemma

The key single-step local postponement: an η-step followed by a parallel β-step
can be reorganized into a parallel β-step followed by η-steps,
`FullEta · ParBeta ⊆ ParBeta · FullEtaStar`.

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-! ## The strong local commutation property -/

theorem WeakPostpone_fullBeta_fullEta :
    WeakPostpone (FullBeta (Var := Var)) (FullEta (Var := Var)) := by
    intros x y z hxy hyz
    induction hyz generalizing x with
    | base hyz => cases hyz with | beta h1 h2 => cases hxy with
      | appL h h4 => exact ⟨_, .single (.base (.beta h1 (FullEta.step_lc_l h4))),
                                FullEta.step_open_cong_r h (FullEta.step_lc_l h4) h4⟩
      | base hxy => cases hxy with | eta hxy =>
          rename_i M N
          have hmn : (M ^ N).LC := by grind
          refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta hmn))⟩
          intros x hx
          apply Xi.appR
          · grind
          · rw [open_lc _ _ _ hxy, open_lc _ _ _ hmn]
            grind
      | appR _ h4 => cases h4 with
        | abs xs ih =>
          rename_i M' N _ M
          have h : M.abs ⭢ηᶠ M'.abs := Xi.abs xs ih
          refine ⟨_, .single (.base (.beta ?_ h2)), FullEta.steps_open_cong_l xs ?_ h2⟩
          · apply FullEta.step_lc_l h
          · grind
        | base h4 => cases h4 with | eta h4 =>
          refine ⟨_, .tail (.trans_left (.single (.base (.beta (LC.abs ∅ _ ?_) h2))) ?_)
                           (.base (.beta h4 h2)),
                     .refl⟩
          · grind
          · unfold open' openRec
            rw [open_lc _ _ _ h4]
            grind
    | abs xs h ih => cases hxy with
      | base hxy => cases hxy with | eta hxy =>
        rename_i M N
        have hmn : M.abs  ⭢βᶠ N.abs := Xi.abs xs h
        have n_lc := FullBeta.step_lc_r hmn
        refine ⟨_, ?_, .single (.base (.eta n_lc))⟩
        apply FullBeta.steps_abs_cong xs
        intros x hx
        unfold open' openRec
        apply FullBeta.transgen_app_l
        · grind
        · unfold openRec
          rw [<- lcAt_iff_LC] at hxy n_lc
          rw [lcAt_openRec_above_lcAt _ _ 1 1, lcAt_openRec_above_lcAt _ _ 1 1]
          all_goals grind
      | abs ys ihh =>
        rename_i M M' N
        have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
        specialize h x (by grind)
        obtain ⟨w, hw1, hw2⟩ := ih x (by grind) (ihh x (by grind))
        have : w.LC := by cases hw1 <;> apply FullBeta.step_lc_r <;> assumption
        refine ⟨(w.close x).abs, ?_, ?_⟩
        · apply FullBeta.steps_abs_cong (∅ ∪ y.fv ∪ z.fv ∪ M.fv ∪ M'.fv ∪ xs ∪ N.fv ∪ ys)
          intros c hc
          unfold close open'
          rw [close_openRec_to_subst]
          · have g := FullBeta.steps_subst_cong_l _ _ (fvar c) x hw1 (by grind)
            rw [subst_open, subst_fvar] at g <;> grind
          · cases hw1 <;> apply FullBeta.step_lc_r <;> assumption
          · grind
        · rw [open_close_var x M' (by grind)]
          apply FullEta.steps_abs_close hw2
          grind
    | appL _ h ih => cases hxy with
      | appL h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                      exact ⟨_, FullBeta.transgen_app_r h1 hw1, FullEta.redex_app_r_cong hw2 h1⟩
      | appR h1 h2 =>
        exact ⟨_, FullBeta.transgen_app_r (FullEta.step_lc_l h2) (.single h),
                  FullEta.redex_app_l_cong (.single h2) (FullBeta.step_lc_r h)⟩
      | base hxy => cases hxy with | eta hxy =>
        refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta (LC.app ?_ (FullBeta.step_lc_r h))))⟩
        · intros x hx
          apply Xi.appR
          · grind
          · apply Xi.appL
            · grind
            · rw [open_lc, open_lc]
              · grind
              · apply FullBeta.step_lc_r h
              · cases hxy
                grind
        · · cases hxy
            grind
    | appR _ h ih => cases hxy with
      | base hxy => cases hxy with | eta hxy =>
        refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta (LC.app (FullBeta.step_lc_r h) ?_)))⟩
        · intros x hx
          apply Xi.appR
          · grind
          · apply Xi.appR
            · grind
            · rw [open_lc, open_lc]
              · grind
              · apply FullBeta.step_lc_r h
              · apply FullBeta.step_lc_l h
        · cases hxy
          grind
      | appL h1 h2 =>
        exact ⟨_, FullBeta.transgen_app_l (FullEta.step_lc_l h2) (.single h),
                  FullEta.redex_app_r_cong (.single h2) (FullBeta.step_lc_r h)⟩
      | appR h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                      exact ⟨_, FullBeta.transgen_app_l h1 hw1, FullEta.redex_app_l_cong hw2 h1⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
