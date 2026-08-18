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
    induction hyz generalizing x with
    | base hyz => cases hyz with | beta h1 h2 => cases hxy with
      | appL h h4 => exact ⟨_, .single (.base (.beta h1 (FullEta.step_lc_l h4))),
                                FullEta.step_open_cong_r h h4⟩
      | base hxy => cases hxy with | eta hxy =>
          rename_i M N
          have hmn : (M ^ N).LC := by grind
          refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta hmn))⟩
          intros x hx
          apply Xi.appR
          · grind
          · rw [open_lc _ _ _ hxy, open_lc _ _ _ hmn]
            grind
      | appR _ h => cases h with
        | abs xs ih =>
          refine ⟨_, .single (.base (.beta (FullEta.step_lc_l (Xi.abs xs ih)) h2)),
                      FullEta.steps_open_cong_l xs ?_ h2⟩
          grind
        | base h => cases h with | eta h =>
          refine ⟨_, .tail (.trans_left (.single (.base (.beta (LC.abs ∅ _ ?_) h2))) ?_)
                           (.base (.beta h h2)),
                     .refl⟩
          · grind
          · unfold openRec
            rw [open_lc _ _ _ h]
            grind
    | abs xs h ih => cases hxy with
      | base hxy => cases hxy with | eta hxy =>
        rename_i M N
        have hmn : M.abs ⭢βᶠ N.abs := Xi.abs xs h
        have n_lc := FullBeta.step_lc_r hmn
        refine ⟨_, FullBeta.steps_abs_cong xs ?_, .single (.base (.eta n_lc))⟩
        intros x hx
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
        refine ⟨(w.close x).abs,
                 FullBeta.steps_abs_cong (∅ ∪ y.fv ∪ z.fv ∪ M.fv ∪ M'.fv ∪ xs ∪ N.fv ∪ ys) ?_,
                 ?_⟩
        · intros c hc
          unfold close open'
          rw [close_openRec_to_subst]
          · have g := FullBeta.steps_subst_cong_l _ _ (fvar c) x hw1 (by grind)
            rw [subst_open, subst_fvar] at g <;> grind
          · cases hw1 <;> apply FullBeta.step_lc_r <;> assumption
          · grind
        · rw [open_close_var x M' (by grind)]
          exact FullEta.steps_abs_close hw2
    | appL _ h ih => cases hxy with
      | appL h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                      exact ⟨_, FullBeta.transgen_app_r h1 hw1, FullEta.redex_app_r_cong hw2 h1⟩
      | appR _ h2 => exact ⟨_, FullBeta.transgen_app_r (FullEta.step_lc_l h2) (.single h),
                               FullEta.redex_app_l_cong (.single h2) (FullBeta.step_lc_r h)⟩
      | base hxy => cases hxy with | eta hxy => cases hxy with | app zlc mlc =>
        refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta (LC.app zlc (FullBeta.step_lc_r h))))⟩
        intros x hx
        apply Xi.appR
        · grind
        · apply Xi.appL
          · grind
          · rw [open_lc, open_lc] <;> grind [FullBeta.step_lc_r]
    | appR _ h ih => cases hxy with
      | base hxy => cases hxy with | eta hxy => cases hxy with | app mlc zlc =>
        refine ⟨_, .single (.abs ∅ ?_), .single (.base (.eta (LC.app (FullBeta.step_lc_r h) zlc)))⟩
        intros x hx
        apply Xi.appR
        · grind
        · apply Xi.appR
          · grind
          · rw [open_lc, open_lc] <;> grind [FullBeta.step_lc_r]
      | appL _ h2 => exact ⟨_, FullBeta.transgen_app_l (FullEta.step_lc_l h2) (.single h),
                               FullEta.redex_app_r_cong (.single h2) (FullBeta.step_lc_r h)⟩
      | appR h1 h2 => obtain ⟨w, hw1, hw2⟩ := ih h2
                      exact ⟨_, FullBeta.transgen_app_l h1 hw1, FullEta.redex_app_l_cong hw2 h1⟩

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
theorem Etastar_normal {P Q : Term Var}
  (h : P ↠ηᶠ Q) (hP : Relation.Normal FullBeta P) : Relation.Normal FullBeta Q := by
  intros hR
  obtain ⟨_, hR⟩ := hR
  obtain ⟨y, hy, _⟩ := eta_beta_postpone h (.single hR)
  apply hP
  rw [Relation.TransGen.head'_iff] at hy
  grind


/-- **A term has a βη-normal form ⇔ it has a β-normal form.** -/
theorem hasBetaEtaNF_iff_hasBetaNF (t : Term Var) :
  Relation.Normalizable FullBeta t ↔ Relation.Normalizable FullBetaEta t := by
  constructor
  · intros hbeta
    obtain ⟨y, hy, hbeta⟩ := hbeta
    obtain ⟨z, hz, hnormal⟩:= Relation.SN.normalizable (FullEta.wellFoundedFullEta.apply y)
    refine ⟨z, .trans (FullBetaEta.from_beta _ _ hy) (FullBetaEta.from_eta _ _ hz), ?_⟩
    have := Etastar_normal hz hbeta
    intros h
    obtain ⟨_, h⟩ := h
    cases h <;> grind
  · intros hbetaeta
    obtain ⟨y, hy, hbetaetanormal⟩ := hbetaeta
    obtain ⟨L, hbeta, heta⟩ := eta_postponement hy
    rw [FullBetaEta.normal_fullbeta_iff] at hbetaetanormal
    obtain ⟨_, _⟩ := hbetaetanormal
    have h : Relation.Normalizable FullBeta y := by exists y
    obtain ⟨W, hw, hnormal⟩ := Etastar_hasBetaNF heta h
    exact ⟨W, .trans hbeta hw, hnormal⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
