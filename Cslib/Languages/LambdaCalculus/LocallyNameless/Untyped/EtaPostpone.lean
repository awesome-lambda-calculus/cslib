/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParEta

/-!  # Takahashi's η/β commutation lemma

This file presents 4 postponement theorems for moving η-reduction behind
β-reduction.

## Main results

* `WeakPostpone_eta_beta`: if `P →ηᶠ Q` and `Q →βᶠ R`, then there is a term
  `S` with `P ↠β+ S` and `S ↠ηᶠ R`. Thus a single full η-step followed by a
  single full β-step can be reordered so that β happens first; the β part is
  nonempty, while the η part may be reflexive.
* `commute_etastar_beta`: if `P ↠ηᶠ Q` and `Q ↠βᶠ R`, then there is a term
  `S` with `P ↠βᶠ S` and `S ↠ηᶠ R`.
* `eta_postpone`: if `P ↠βηᶠ Q`, then there is a term `L` such that
  `P ↠βᶠ L` and `L ↠ηᶠ Q`.
* `diamondcommute_etaplus_betastar`: if `P →ηᶠ Q` and `Q →β+ R`, then there is
  a term `S` with `P ↠β+ S` and `S ↠ηᶠ R`.

## Reference

* [Y. Takahashi, *Parallel Reductions in λ-Calculus*][Takahashi1995]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation Function

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- An η-step followed by a β-step can be postponed: if `P →ηᶠ Q` and `Q →βᶠ R`,
then there exists `S` such that `TransGen FullBeta P S` and `S ↠ηᶠ R`.
The β-reduction from `P` to `S` is nonempty, while the η-reduction may take zero steps. -/
theorem WeakPostpone_eta_beta : WeakPostpone (swap (FullEta (Var := Var))) FullBeta := by
  intros y z x hβ hη
  induction hη generalizing z with
  | base hη => cases hη with | eta hη =>
  exact ⟨Term.abs (z.app (bvar 0)),
        .single (.base (.eta (FullBeta.step_lc_r hβ))),
        FullBeta.steps_abs_cong ∅ (fun x hx => FullBeta.transgen_app_l (.fvar _)
                  (.single (by rwa [open_lc _ _ _ hη, open_lc _ _ _ (FullBeta.step_lc_r hβ)])))⟩
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
                    exact FullEta.redex_app_l_cong hw1 h1
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
            exact lcAt_le _ _ _ (by omega) hm
  | abs xs hx ih => cases hβ with
    | base hβ => cases hβ | abs ys hy =>
      rename_i _ _ N
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨w, hw1, hw2⟩ := ih x (by grind) (hy x (by grind))
      refine ⟨(w ^* x).abs, ?_, FullBeta.steps_abs_cong (free_union [fv] Var) ?_⟩
      · rw [open_close_var x N (by grind)]
        rw [reflTransGen_swap] at *
        exact FullEta.steps_abs_close hw1
      · intros c hc
        rw [close_open_to_subst _ _ _ ?_ (by grind)]
        · have g := FullBeta.steps_subst_cong_l _ _ (fvar c) x hw2 (by grind)
          rw [subst_open, subst_fvar] at g <;> grind
        · cases hw2 <;> apply FullBeta.step_lc_r <;> assumption

/-- An η-reduction followed by a β-reduction can be postponed: if `P ↠ηᶠ Q` and
`Q ↠βᶠ R`, then there exists `S` such that `P ↠βᶠ S` and `S ↠ηᶠ R`. -/
theorem commute_etastar_beta : Commute (swap FullEta) (FullBeta (Var := Var)) := by
  intros _ _ _ hη hβ
  simp only [<- reflTransGen_parallel_fullBeta] at hβ
  rw [reflTransGen_swap] at hη
  simp only [<-  reflTransGen_parallel_fullEta] at hη
  rw [<- reflTransGen_swap] at hη
  obtain ⟨s, _, g⟩ := DiamondCommute.to_commute parEta_parBeta_postpone hη hβ
  refine ⟨s, by simp_all [← reflTransGen_parallel_fullBeta], ?_⟩
  rw [reflTransGen_swap] at *
  exact reflTransGen_le_of_le ParEta.le_reflTransGen_fullEta _ _ g

theorem eta_postpone {M N : Term Var} (h : M ↠βηᶠ N) : ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  have g := (commute_equivalents.out 2 4 rfl rfl).mp (commute_etastar_beta (Var := Var)) N M
  rw [sup_comm, reflTransGen_swap] at g
  obtain ⟨L, g, _⟩ := g h
  rw [reflTransGen_swap] at g
  grind

/-- If `P ↠η Q` and `Q ⟶β R`, then there is some `P'` with `P ⟶β P'` and
`P' ↠η R`. This is the diamond-commutation form of βη-postponement.
-/
theorem diamondcommute_etaplus_betastar :
    DiamondCommute (ReflTransGen (swap FullEta)) (TransGen (FullBeta (Var := Var))) :=
  star_over_plus _ _ (single_over_plus _ _ commute_etastar_beta WeakPostpone_eta_beta)

/-- **[Takahashi1995] 3.7.**  If `P ↠ηᶠ Q` and `P` is a β-normal form,
  then `Q` is a β-normal form. -/
theorem etastar_preserves_normal_beta :
  Preserves (ReflTransGen (FullEta (Var := Var))) (Normal FullBeta) := by
  rintro _ _ steps hP ⟨_, hR⟩
  rw [reflTransGen_swap] at steps
  obtain ⟨y, hy, _⟩ := diamondcommute_etaplus_betastar steps (.single hR)
  rw [TransGen.head'_iff] at hy
  exact hP (by grind)

theorem Etastar_hasBetaNF {P Q : Term Var} (steps : P ↠ηᶠ Q)
  (hQ : Normalizable FullBeta Q) : Normalizable FullBeta P := by
  induction steps with
  | refl => grind
  | tail _ step ih => exact ih (parEta_hasBetaNF (FullEta.le_parallel _ _ step) hQ)

/-- **A term has a βη-normal form ⇔ it has a β-normal form.** -/
theorem hasBetaEtaNF_iff_hasBetaNF (t : Term Var) :
  Normalizable FullBeta t ↔ Normalizable FullBetaEta t := by
  refine ⟨fun ⟨y, hy, hβ⟩ => ?_, fun ⟨y, hy, hβηnormal⟩ => ?_⟩
  · obtain ⟨z, hz, hnormal⟩ := SN.normalizable (FullEta.wellFounded.apply y)
    refine ⟨z, .trans (.mono le_sup_left _ _ hy) (.mono le_sup_right _ _ hz), fun ⟨_, h⟩ => ?_⟩
    have := etastar_preserves_normal_beta hz hβ
    cases h <;> grind
  · obtain ⟨L, hβ, hη⟩ := eta_postpone hy
    rw [FullBetaEta.normal_fullbeta_iff] at hβηnormal
    obtain ⟨_, _⟩ := hβηnormal
    have h : Normalizable FullBeta y := by exists y
    obtain ⟨W, hw, hnormal⟩ := Etastar_hasBetaNF hη h
    exact ⟨W, .trans hβ hw, hnormal⟩

theorem Etastar_iff_hasBetaNF {P Q : Term Var} (steps : P ↠ηᶠ Q) :
  Normalizable FullBeta P ↔ Normalizable FullBeta Q := by
  refine ⟨fun hP => ?_, fun hQ => Etastar_hasBetaNF steps hQ⟩
  rw [hasBetaEtaNF_iff_hasBetaNF] at *
  obtain ⟨Z, βηsteps, hZ⟩ := hP
  obtain ⟨_, refl_steps, _⟩ := confluent_beta_eta βηsteps (.mono le_sup_right _ _ steps)
  have := Normal.reflTransGen_eq hZ refl_steps
  subst_vars
  grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
