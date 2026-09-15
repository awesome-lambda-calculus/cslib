/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParEta

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

open Relation Function

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-! ## The strong local commutation property -/

theorem WeakPostpone_fullBeta_fullEta :
    WeakPostpone (swap (FullEta (Var := Var))) (FullBeta (Var := Var)) := by
  intros x y z hβ hη
  induction hη generalizing y with
  | base hη => cases hη with | eta hη =>
  refine ⟨Term.abs (y.app (bvar 0)),
          .single (.base (.eta (FullBeta.step_lc_r hβ))),
          FullBeta.steps_abs_cong ∅ (fun x hx => FullBeta.transgen_app_l (by grind) (.single ?_))⟩
  rw [open_lc _ _ _ hη, open_lc _ _ _ (FullBeta.step_lc_r hβ)]
  grind
  | appL _ h ih => cases hβ with
    | base hβ => cases hβ with | beta hm hn =>
      refine ⟨_, ?_, .single (.base (.beta hm (FullEta.step_lc_l h)))⟩
      rw [reflTransGen_swap] at *
      exact FullEta.step_open_cong_r hm h
    | appL h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                    refine ⟨_, ?_, FullBeta.transgen_app_r h1 hw2⟩
                    rw [reflTransGen_swap] at *
                    exact FullEta.redex_app_r_cong hw1 h1
    | appR _ h2 =>  exact ⟨_, .single (.appL (FullBeta.step_lc_r h2) h),
                              .single (.appR (FullEta.step_lc_l h) h2)⟩
  | appR _ h ih => cases hβ with
    | appL _ h2 => exact ⟨_, .single (.appR (FullBeta.step_lc_r h2) h),
                             .single (.appL (FullEta.step_lc_l h) h2)⟩
    | appR h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                    refine ⟨_, ?_, FullBeta.transgen_app_l h1 hw2⟩
                    rw [reflTransGen_swap] at *
                    exact  FullEta.redex_app_l_cong hw1 h1
    | base hβ => cases hβ with | beta hm hz => cases h with
      | abs xs h => refine ⟨_, ?_, .single (.base (.beta (FullEta.step_lc_l (Xi.abs xs h)) hz))⟩
                    rw [reflTransGen_swap] at *
                    exact FullEta.steps_open_cong_l xs (by grind) hz
      | base h => cases h with | eta h =>
          refine ⟨_, ?_, .head (.base (.beta ?_ hz)) (.single (.base (.beta ?_ (by grind))))⟩
          · rw [<- lcAt_iff_LC] at *
            rw [lcAt_openRec_above_lcAt _ _ 1 _ (by omega) (by grind)]
            grind
          · rw [<- lcAt_iff_LC] at *
            simp_all only [LcAt, zero_add, Order.lt_one_iff, decide_true, Bool.and_true]
            apply lcAt_le _ _ _ (by omega) hm
          · rw [<- lcAt_iff_LC] at *
            simp_all only [LcAt, zero_add]
            rw [lcAt_openRec_iff_lcAt _ _ _ (lcAt_le _ _ _ (by omega) hz)]
            apply lcAt_le _ _ _ (by omega) hm
  | abs xs hx ih => cases hβ with
    | base hβ => cases hβ
    | abs ys hy =>
      rename_i _ _ N
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨w, hw1, hw2⟩ := ih x (by grind) (hy x (by grind))
      refine ⟨(w.close x).abs, ?_, FullBeta.steps_abs_cong (free_union [fv] Var) ?_⟩
      · rw [open_close_var x N (by grind)]
        rw [reflTransGen_swap] at *
        exact FullEta.steps_abs_close hw1
      · intros c hc
        unfold close open'
        rw [close_openRec_to_subst]
        · have g := FullBeta.steps_subst_cong_l _ _ (fvar c) x hw2 (by grind)
          rw [subst_open, subst_fvar] at g <;> grind
        · cases hw2 <;> apply FullBeta.step_lc_r <;> assumption
        · grind

theorem localpostpone_Beta_Eta : Commute (swap FullEta) (FullBeta (Var := Var)) := by
  intros _ _ _ hη hβ
  simp only [<- reflTransGen_parallel_fullBeta] at hβ
  rw [reflTransGen_swap] at hη
  simp only [<-  reflTransGen_parallel_fullEta] at hη
  rw [<- reflTransGen_swap] at hη
  obtain ⟨s, _, g⟩ := DiamondCommute.to_commute parEta_parBeta_postpone hη hβ
  refine ⟨s, ?_, ?_⟩
  · simp_all [<- reflTransGen_parallel_fullBeta]
  · rw [reflTransGen_swap] at *
    exact reflTransGen_le_of_le ParEta.le_reflTransGen_fullEta _ _ g

theorem eta_postponement {M N : Term Var} (h : M ↠βηᶠ N) :
    ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  have g := (commute_equivalents.out 2 4 rfl rfl).mp (localpostpone_Beta_Eta (Var := Var)) N M
  rw [sup_comm, reflTransGen_swap] at g
  obtain ⟨L, g, _⟩ := g h
  rw [reflTransGen_swap] at g
  grind

theorem eta_beta_postpone :
    DiamondCommute (ReflTransGen (swap FullEta)) (TransGen (FullBeta (Var := Var))) :=
  star_over_plus _ _ (single_over_plus _ _ localpostpone_Beta_Eta WeakPostpone_fullBeta_fullEta)

/-- **Takahashi's Lemma 3.7.**  If `P ⟹_η Q` (parallel η-reduction) and `P` is a
β-normal form, then `Q` is a β-normal form.

The proof uses strong η-postponement: a single parallel η-step is an η-reduction
`P ↠η Q`, so any β-step `Q ⟶β R` would give, by `eta_beta_postpone`, a non-empty
β-reduction `P ⟶β⁺ ⋯`, contradicting β-normality of `P`. -/
theorem etastar_preserves_normal_beta :
  Relation.Preserves (Relation.ReflTransGen (FullEta (Var := Var))) (Relation.Normal FullBeta) := by
  rintro _ _ steps hP ⟨_, hR⟩
  rw [reflTransGen_swap] at steps
  obtain ⟨y, hy, _⟩ := eta_beta_postpone steps (.single hR)
  apply hP
  rw [Relation.TransGen.head'_iff] at hy
  grind

theorem Etastar_hasBetaNF {P Q : Term Var}
    (h : P ↠ηᶠ Q) (hQ : Relation.Normalizable FullBeta Q) : Relation.Normalizable FullBeta P := by
  induction h with
  | refl => grind
  | tail _ h ih => exact ih (parEta_hasBetaNF (FullEta.le_parallel _ _ h) hQ)

/-- **A term has a βη-normal form ⇔ it has a β-normal form.** -/
theorem hasBetaEtaNF_iff_hasBetaNF (t : Term Var) :
  Relation.Normalizable FullBeta t ↔ Relation.Normalizable FullBetaEta t := by
  constructor
  · rintro ⟨y, hy, hβ⟩
    obtain ⟨z, hz, hnormal⟩:= Relation.SN.normalizable (FullEta.wellFounded.apply y)
    refine ⟨z, .trans (Relation.ReflTransGen.mono le_sup_left _ _ hy)
                      (Relation.ReflTransGen.mono le_sup_right _ _ hz), ?_⟩
    have := etastar_preserves_normal_beta hz hβ
    rintro ⟨_, h⟩
    cases h <;> grind
  · rintro ⟨y, hy, hβetanormal⟩
    obtain ⟨L, hβ, hη⟩ := eta_postponement hy
    rw [FullBetaEta.normal_fullbeta_iff] at hβetanormal
    obtain ⟨_, _⟩ := hβetanormal
    have h : Relation.Normalizable FullBeta y := by exists y
    obtain ⟨W, hw, hnormal⟩ := Etastar_hasBetaNF hη h
    exact ⟨W, .trans hβ hw, hnormal⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
