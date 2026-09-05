/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

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

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-! ## The strong local commutation property -/

theorem WeakPostpone_fullBeta_fullEta :
    WeakPostpone (FullBeta (Var := Var)) (FullEta (Var := Var)) := by
  intros x y z hxy hyz
  induction hxy generalizing z with
  | base hxy => cases hxy with | eta hxy =>
  refine ⟨Term.abs (z.app (bvar 0)),
          FullBeta.steps_abs_cong ∅ (fun x hx => FullBeta.transgen_app_l (by grind) (.single ?_)),
          .single (.base (.eta (FullBeta.step_lc_r hyz)))⟩
  rw [open_lc _ _ _ hxy, open_lc _ _ _ (FullBeta.step_lc_r hyz)]
  grind
  | appL _ h ih => cases hyz with
    | base hyz => cases hyz with | beta hm hn =>
      exact ⟨_, .single (.base (.beta hm (FullEta.step_lc_l h))), FullEta.step_open_cong_r hm h⟩
    | appL h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                    exact ⟨_, FullBeta.transgen_app_r h1 hw1, FullEta.redex_app_r_cong hw2 h1⟩
    | appR _ h2 =>  exact ⟨_, .single (.appR (FullEta.step_lc_l h) h2),
                              .single (.appL (FullBeta.step_lc_r h2) h)⟩
  | appR _ h ih => cases hyz with
    | appL _ h2 => exact ⟨_, .single (.appL (FullEta.step_lc_l h) h2),
                             .single (.appR (FullBeta.step_lc_r h2) h)⟩
    | appR h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                    exact ⟨_, FullBeta.transgen_app_l h1 hw1, FullEta.redex_app_l_cong hw2 h1⟩
    | base hyz => cases hyz with | beta hm hz => cases h with
      | abs xs h => exact ⟨_, .single (.base (.beta (FullEta.step_lc_l (Xi.abs xs h)) hz)),
                              FullEta.steps_open_cong_l xs (by grind) hz⟩
      | base h => cases h with | eta h =>
          refine ⟨_, .head (.base (.beta ?_ hz)) (.single (.base (.beta ?_ (by grind)))), ?_⟩
          · rw [<- lcAt_iff_LC] at *
            simp_all only [LcAt, zero_add, Order.lt_one_iff, decide_true, Bool.and_true]
            apply lcAt_le _ _ _ (by omega) hm
          · rw [<- lcAt_iff_LC] at *
            simp_all only [LcAt, zero_add]
            rw [lcAt_openRec_iff_lcAt _ _ _ (lcAt_le _ _ _ (by omega) hz)]
            apply lcAt_le _ _ _ (by omega) hm
          · rw [<- lcAt_iff_LC] at *
            rw [lcAt_openRec_above_lcAt _ _ 1 _ (by omega) (by grind)]
            grind
  | abs xs hx ih => cases hyz with
    | base hyz => cases hyz
    | abs ys hy =>
      rename_i _ _ N
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨w, hw1, hw2⟩ := ih x (by grind) (hy x (by grind))
      refine ⟨(w.close x).abs, FullBeta.steps_abs_cong (free_union [fv] Var) ?_, ?_⟩
      · intros c hc
        unfold close open'
        rw [close_openRec_to_subst]
        · have g := FullBeta.steps_subst_cong_l _ _ (fvar c) x hw1 (by grind)
          rw [subst_open, subst_fvar] at g <;> grind
        · cases hw1 <;> apply FullBeta.step_lc_r <;> assumption
        · grind
      · rw [open_close_var x N (by grind)]
        exact FullEta.steps_abs_close hw2

theorem Etastar_hasBetaNF {P Q : Term Var}
    (h : P ↠ηᶠ Q) (hQ : Relation.Normalizable FullBeta Q) : Relation.Normalizable FullBeta P := by
  induction h with
  | refl => grind
  | tail _ h ih => exact ih (parEta_hasBetaNF (ParEta.fromFullEta h) hQ)

theorem localpostpone_fullBeta_fullEta :
  LocalPostpone (Relation.ReflTransGen (FullBeta (Var := Var))) (Relation.ReflTransGen FullEta) :=
  by
    intros _ _ _ heta hbeta
    simp only [<- reflTransGen_parallel_fullBeta] at hbeta
    rw [<- paraEtachain_iff_redex] at heta
    obtain ⟨s, _, _⟩ := postpone_ab parEta_parBeta_postpone heta hbeta
    use s
    simp_all [<- reflTransGen_parallel_fullBeta, <- paraEtachain_iff_redex]

theorem eta_postponement {M N : Term Var} (h : M ↠βηᶠ N) :
    ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  induction h with
  | refl => exists M
  | tail _ h ih =>
      obtain ⟨L, hbeta, heta⟩ := ih
      cases h with
      | inl h =>  obtain ⟨P, hpbeta, hpeta⟩ := localpostpone_fullBeta_fullEta heta (.single h)
                  exact ⟨P, .trans hbeta hpbeta, hpeta⟩
      | inr _ => grind

theorem eta_beta_postpone :
    LocalPostpone (Relation.TransGen (FullBeta (Var := Var))) (Relation.ReflTransGen FullEta) := by
  intros _ _ _ heta hbeta
  exact star_over_plus localpostpone_fullBeta_fullEta WeakPostpone_fullBeta_fullEta heta hbeta

/-- **Takahashi's Lemma 3.7.**  If `P ⟹_η Q` (parallel η-reduction) and `P` is a
β-normal form, then `Q` is a β-normal form.

The proof uses strong η-postponement: a single parallel η-step is an η-reduction
`P ↠η Q`, so any β-step `Q ⟶β R` would give, by `eta_beta_postpone`, a non-empty
β-reduction `P ⟶β⁺ ⋯`, contradicting β-normality of `P`. -/
theorem etastar_preserves_normal_beta :
  Relation.Preserves (Relation.ReflTransGen (FullEta (Var := Var))) (Relation.Normal FullBeta) := by
  rintro _ _ steps hP ⟨_, hR⟩
  obtain ⟨y, hy, _⟩ := eta_beta_postpone steps (.single hR)
  apply hP
  rw [Relation.TransGen.head'_iff] at hy
  grind


/-- **A term has a βη-normal form ⇔ it has a β-normal form.** -/
theorem hasBetaEtaNF_iff_hasBetaNF (t : Term Var) :
  Relation.Normalizable FullBeta t ↔ Relation.Normalizable FullBetaEta t := by
  constructor
  · rintro ⟨y, hy, hbeta⟩
    obtain ⟨z, hz, hnormal⟩:= Relation.SN.normalizable (FullEta.wellFoundedFullEta.apply y)
    refine ⟨z, .trans (Relation.ReflTransGen.mono le_sup_left _ _ hy)
                      (Relation.ReflTransGen.mono le_sup_right _ _ hz), ?_⟩
    have := etastar_preserves_normal_beta hz hbeta
    rintro ⟨_, h⟩
    cases h <;> grind
  · rintro ⟨y, hy, hbetaetanormal⟩
    obtain ⟨L, hbeta, heta⟩ := eta_postponement hy
    rw [FullBetaEta.normal_fullbeta_iff] at hbetaetanormal
    obtain ⟨_, _⟩ := hbetaetanormal
    have h : Relation.Normalizable FullBeta y := by exists y
    obtain ⟨W, hw, hnormal⟩ := Etastar_hasBetaNF heta h
    exact ⟨W, .trans hbeta hw, hnormal⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
