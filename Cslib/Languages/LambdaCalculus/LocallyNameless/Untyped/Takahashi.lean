/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.TakahashiSupport
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract

/-!
# Takahashi's η/β commutation lemma

The key single-step local postponement: an η-step followed by a parallel β-step
can be reorganized into a parallel β-step followed by η-steps,
`FullEta · ParBeta ⊆ ParBeta · FullEtaStar`.

This is exactly `AbstractPostpone.LocalPostpone ParBeta FullEta`.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- The statement proved by induction: η postpones over a single parallel β-step
out of `M`. -/
def TakaProp (M : Term Var) : Prop :=
  ∀ N P : Term Var, FullEta M N → Parallel N P → ∃ Q, Parallel M Q ∧ Q ↠ηᶠ P


/-
Base case: the η-redex is at the top.
-/
theorem taka_base {M0 P : Term Var} (hM0 : LC M0) (hp : Parallel M0 P) :
    ∃ Q, Parallel (Term.abs (Term.app M0 (Term.bvar 0))) Q ∧ Q ↠ηᶠ P := by
  exists Term.abs ( Term.app P ( Term.bvar 0 ) )
  constructor
  · apply Parallel.abs ( ∅ : Finset Var )
    intro x hx
    unfold open' openRec
    convert Parallel.app _ _ <;> grind
  · convert Relation.ReflTransGen.single ( Xi.base ( Eta.eta _ ) )
    apply para_lc_r hp

/-
The η-step is in the argument of an application.
-/
theorem taka_appL {Z M0 N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (Term.app Z M0) → TakaProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hp : Parallel (Term.app Z N0) P) :
    ∃ Q, Parallel (Term.app Z M0) Q ∧ Q ↠ηᶠ P := by
  cases hp with
  | app _ _ =>
  · obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 (Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ) N0 _ he ‹_›
    exact ⟨ _, Parallel.app ‹_› hQ₁, FullEta.redex_app_r_cong (by grind) (by grind) ⟩
  | beta xs hk₁ hk₂ =>
    rename_i N M M'
    obtain ⟨ Q0, hQ0par, hQ0eta ⟩ := ih M0 (by grind) N0 _ he hk₂
    exists M ^ Q0
    constructor
    · exact Parallel.beta _ hk₁ hQ0par
    · refine FullEta.steps_open_cong_r ?_ (by grind) hQ0eta
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      specialize hk₁ x (by grind)
      apply para_lc_r at hk₁
      apply open_abs_lc hk₁

/-
The β-redex obtained by η-contracting the operator `abs (app (abs M1) (bvar 0))`
to `abs M1` is reached in a single parallel β-step.
-/
omit [DecidableEq Var] in
theorem parBeta_eta_redex {M1 M1' Z Z' : Term Var} (xs : Finset Var)
    (hLC : LC (Term.abs M1))
    (hbody : ∀ x ∉ xs, Parallel (M1 ^ fvar x) (M1' ^ fvar x))
    (hZZ : Parallel Z Z') :
    Parallel (Term.app (Term.abs (Term.app (Term.abs M1) (Term.bvar 0))) Z) (M1' ^ Z') := by
  apply Parallel.beta xs _ hZZ
  intro x hx
  apply Parallel.beta xs
  · intro x hx
    rw [lcAt_openRec_above_lcAt _ _ 1]
    · apply hbody x hx
    · omega
    · rw [<- lcAt_iff_LC] at hLC
      grind
  · grind

/-
The β-redex-creation subcase where the operator is itself an abstraction
with an η-reduction inside.
-/
theorem taka_appR_create_abs {A M1 M1' Z N1' : Term Var} (ys2 xs : Finset Var)
    (ih : ∀ (M' : Term Var), size M' < size (Term.app (Term.abs A) Z) → TakaProp M')
    (hA : ∀ x ∉ ys2, FullEta (A ^ fvar x) (M1 ^ fvar x))
    (hbody : ∀ x ∉ xs, Parallel (M1 ^ fvar x) (M1' ^ fvar x))
    (hZN1' : Parallel Z N1') :
    ∃ Q, Parallel (Term.app (Term.abs A) Z) Q ∧ Q ↠ηᶠ (M1' ^ N1') := by
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  -- By `TakaProp`, we have `∃ W, ParBeta (A ^ fvar z) W ∧ FullEtaStar W (M1' ^ fvar z)`.
  obtain ⟨W, hWpar, hWeta⟩ : ∃ W, Parallel (A ^ (fvar z)) W ∧ W ↠ηᶠ (M1' ^ (fvar z)) :=
    ih _ (by grind [size_openRec_fvar]) _ _ (hA _ (by grind)) (hbody _ (by grind))
  convert exists_Q_app_abs z (by grind) (by grind) hWpar hWeta hZN1'

/-
The η-step is in the operator of an application (includes the β-redex
creation case).
-/
theorem taka_appR {Z M0 N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (Term.app M0 Z) → TakaProp M')
    (he : FullEta M0 N0) (hp : Parallel (Term.app N0 Z) P) :
    ∃ Q, Parallel (Term.app M0 Z) Q ∧ Q ↠ηᶠ P := by
  cases hp with
  | app _ _ =>
    obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 (Nat.lt_succ_of_le ( Nat.le_add_right _ _ ) ) N0 _ he ‹_›
    exact ⟨ _, Parallel.app hQ₁ ‹_›, FullEta.redex_app_l_cong  hQ₂ (by grind)⟩
  | beta xs hM hN => cases he with
    | base hM' =>
        cases hM'
        exact ⟨ _, parBeta_eta_redex _ ‹_› hM hN, Relation.ReflTransGen.refl ⟩
    | abs xs _ => apply taka_appR_create_abs <;> tauto

/-
The η-step is under a binder.
-/
theorem taka_abs {M0 N0 P : Term Var} (xs : Finset Var)
    (ih : ∀ (M' : Term Var), size M' < size (Term.abs M0) → TakaProp M')
    (hbody : ∀ x ∉ xs, FullEta (M0 ^ fvar x) (N0 ^ fvar x))
    (hp : Parallel (Term.abs N0) P) :
    ∃ Q, Parallel (Term.abs M0) Q ∧ Q ↠ηᶠ P := by
  cases hp with
  | abs xs' hbody' =>
  rename_i  M'
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  specialize ih ( M0 ^ fvar z ) ?_ ( N0 ^ fvar z ) ( M' ^ fvar z ) ?_ ?_
  · simp +decide [ Term.size ]
  · aesop
  · aesop
  · exact exists_Q_abs z (by grind) (by grind) ih.choose_spec.1 ih.choose_spec.2

/-- **Takahashi's lemma.** η postpones over a single parallel β-step. -/
theorem eta_par_local (M : Term Var) : TakaProp M := by
  have key : ∀ n (M : Term Var), size M = n → TakaProp M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro M hMn N P he hp
      have ih : ∀ (M' : Term Var), size M' < size M → TakaProp M' := by
        intro M' hM'
        exact IH (size M') (hMn ▸ hM') M' rfl
      cases he with
      | base hb =>
          cases hb with
          | eta hM0 => exact taka_base hM0 hp
      | appL hZ hxi => exact taka_appL ih hZ hxi hp
      | appR hZ hxi => exact taka_appR ih hxi hp
      | abs xs hbody => exact taka_abs xs ih hbody hp
  intro N P he hp
  exact key (size M) M rfl N P he hp

/-- The local postponement hypothesis instantiated for parallel β and η. -/
theorem localPostpone_parBeta_fullEta :
    LocalPostpone (Parallel (Var := Var)) (FullEta (Var := Var)) :=
  fun _ _ _ he hp => eta_par_local _ _ _ he hp


/-
**η-postponement.** If `M` reduces to `N` under combined βη-reduction, then
there is an intermediate term `L` with `M ⟶β* L` and `L ⟶η* N`: every η-step can
be postponed past the β-steps.
-/
theorem eta_postponement {M N : Term Var} (h : M ↠βηᶠ N) :
    ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  obtain ⟨L, hL₁, hL₂⟩ := postpone localPostpone_parBeta_fullEta (.mono (fun a b hab => by
    cases hab <;> [exact Or.inl (step_to_para ‹_›); exact Or.inr ‹_›]) h)
  rw [parachain_iff_redex] at hL₁
  exact ⟨ L, hL₁, hL₂ ⟩




/-! ## The strong local commutation property -/

/-- The property proved by strong induction: a single η-step followed by a single
β-step out of `M` reorganizes into a non-empty β-sequence followed by η-steps. -/
def TakaPlusProp (M : Term Var) : Prop :=
  ∀ N P : Term Var, FullEta M N → FullBeta N P →
    ∃ Q, Relation.TransGen FullBeta M Q ∧ Q ↠ηᶠ P


/-
Base case: the η-redex is at the top.
-/
theorem takaP_base {M0 P : Term Var} (hM0 : LC M0) (hbeta : FullBeta M0 P) :
    ∃ Q, Relation.TransGen FullBeta (abs (app M0 (bvar 0))) Q ∧ Q ↠ηᶠ P := by
  exists abs ( app P ( bvar 0 ) )
  constructor
  · apply Relation.TransGen.single
    apply Xi.abs ∅
    intros x hx
    unfold open' openRec
    rw [open_lc _ _ M0 hM0, open_lc _ _ P] <;> grind [FullBeta.step_lc_r]
  · exact .single ( Xi.base ( Eta.eta (FullBeta.step_lc_r hbeta) ) )

/-
η-step in the argument of an application.
-/
theorem takaP_appL {Z M0 N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app Z M0) → TakaPlusProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hbeta : FullBeta (app Z N0) P) :
    ∃ Q, Relation.TransGen FullBeta (app Z M0) Q ∧ Q ↠ηᶠ P := by
  rcases hbeta with ( _ | _ | _ | _ )
  · rcases ‹_› with ( _ | _ | _ | _ )
    rcases ‹Beta _ _› with ( _ | _ | _ | _ )
    rename_i k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆
    refine ⟨ _, Relation.TransGen.single (Xi.base (Beta.beta hZ (FullEta.step_lc_l he) ) ), ?_ ⟩
    apply FullEta.step_open_cong_r hZ (FullEta.step_lc_l he) he
  · obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 (Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ) N0 _ he ‹_›
    exact ⟨ _, FullBeta.transgen_app_r hZ hQ₁, (FullEta.redex_app_r_cong hQ₂ (by assumption))⟩
  · rename_i N hN hN'
    exact ⟨ _, FullBeta.transgen_app_l (FullEta.step_lc_l he) (.single hN),
               FullEta.redex_app_r_cong (.single he) (FullBeta.step_lc_r hN)⟩

/-
η-step in the operator of an application (includes β-redex creation).
-/
theorem takaP_appR {M0 Z N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app M0 Z) → TakaPlusProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hbeta : FullBeta (app N0 Z) P) :
    ∃ Q, Relation.TransGen FullBeta (app M0 Z) Q ∧ Q ↠ηᶠ P := by
  cases hbeta with
  | appL hN hN' =>
    rename_i N
    refine ⟨ _, FullBeta.transgen_app_r ?_ ( Relation.TransGen.single hN' ), ?_ ⟩
    · apply FullEta.step_lc_l
      assumption
    · grind +suggestions
  | appR hZ' hN =>
    rename_i N
    specialize ih M0 (by simp +decide [ Term.size ]) N0 N he (by tauto)
    obtain ⟨w, hw1, hw2⟩ := ih
    refine ⟨ _, FullBeta.transgen_app_l hZ' hw1, FullEta.redex_app_l_cong hw2 hZ'⟩
  | base hbeta => cases hbeta with | beta _ _ => cases he with
    | base he => cases he with | eta he =>
      rename_i M _ _
      exists M ^ Z
      constructor
      · apply Relation.TransGen.tail
        · apply Relation.TransGen.single
          apply Xi.base
          constructor
          · apply LC.abs ∅
            intros x hx
            constructor
            rw [open_lc] <;> grind
            grind
          · assumption
        · apply Xi.base
          unfold open'
          conv =>
            left
            unfold openRec
          rw [open_lc]
          · constructor <;> grind
          · assumption
      · grind
    | abs xs hL =>
      rename_i L
      exists L ^ Z
      constructor
      · apply Relation.TransGen.single
        apply Xi.base
        constructor
        · have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
          specialize hL x (by grind)
          apply FullEta.step_lc_l at hL
          apply open_abs_lc hL
        · assumption
      · apply open_body
        intros x hx
        · specialize hL x hx
          grind
        · grind

/-
η-step under a binder.
-/
theorem takaP_abs {M0 N0 P : Term Var} (xs : Finset Var)
    (ih : ∀ (M' : Term Var), size M' < size (abs M0) → TakaPlusProp M')
    (hbody : ∀ x ∉ xs, FullEta (M0 ^ fvar x) (N0 ^ fvar x))
    (hbeta : FullBeta (abs N0) P) :
    ∃ Q, Relation.TransGen FullBeta (abs M0) Q ∧ Q ↠ηᶠ P := by
  cases hbeta with
  | base _ => cases ‹Beta N0.abs P›
  | abs ys hbeta =>
    rename_i N
    have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
    obtain ⟨Q, hqbeta, hqeta⟩ :=
      ih (M0 ^ fvar z) (by simp) (N0 ^ fvar z) (‹_› ^ fvar z) (hbody z (by grind)) (by grind)
    exists (Q.close z).abs
    have qlc : Q.LC := by refine Xi.steps_lc_r ?_  hqbeta
                          intros _ _ _
                          apply FullBeta.step_lc_r
                          assumption
    rw [<- close_open z Q qlc] at hqbeta hqeta
    constructor
    · apply FullBeta.steps_abs_cong (∅ ∪ M0.fv ∪ N0.fv ∪ xs ∪ N.fv ∪ ys ∪ {z})
      · intros x hx
        have h := FullBeta.steps_subst_cong_l _ _  (fvar x) z hqbeta (by grind)
        rw [subst_open _ _ _ _ (by grind)] at h
        rw [subst_open _ _ _ _ (by grind)] at h
        rw [subst_fresh _ _ _ (by grind)] at h
        rw [subst_fresh _ (Q ^* z) _ (by grind)] at h
        rw [subst_fvar] at h
        split at h <;> grind
    · apply FullEta.redex_abs_cong (∅ ∪ M0.fv ∪ N0.fv ∪ xs ∪ N.fv ∪ ys ∪ {z})
      · intros x hx
        have h := @FullEta.steps_subst_cong_l _ _ _ z _ _ (fvar x) hqeta (by grind)
        rw [subst_open _ _ _ _ (by grind)] at h
        rw [subst_open _ _ _ _ (by grind)] at h
        rw [subst_fresh _ _ _ (by grind)] at h
        rw [subst_fresh _ N _ (by grind)] at h
        rw [subst_fvar] at h
        split at h <;> grind
      · apply LC.abs ∅
        intros x hx
        rw [close_open_to_subst]
        apply subst_lc <;> grind
        all_goals grind

/-- **Strong local commutation.** A single η-step followed by a single β-step
reorganizes into a non-empty β-sequence followed by η-steps. -/
theorem eta_beta_local (M : Term Var) : TakaPlusProp M := by
  have key : ∀ n (M : Term Var), size M = n → TakaPlusProp M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro M hMn N P he hbeta
      have ih : ∀ (M' : Term Var), size M' < size M → TakaPlusProp M' := by
        intro M' hM'
        exact IH (size M') (hMn ▸ hM') M' rfl
      cases he with
      | base hb =>
          cases hb with
          | eta hM0 => exact takaP_base hM0 hbeta
      | appL hZ hxi => exact takaP_appL ih hZ hxi hbeta
      | appR hZ hxi => exact takaP_appR ih hZ hxi hbeta
      | abs xs hbody => exact takaP_abs xs ih hbody hbeta
  intro N P he hbeta
  exact key (size M) M rfl N P he hbeta

/-- The strong local postponement hypothesis instantiated for full β and η. -/
theorem strongLocal_fullBeta_fullEta :
    StrongLocal (FullBeta (Var := Var)) (FullEta (Var := Var)) :=
  fun _ _ _ he hbeta => eta_beta_local _ _ _ he hbeta

/-
Weak commutation of full β and full η (derived from η-postponement via the
parallel-β local lemma).
-/
theorem weakCommute_fullBeta_fullEta :
    WeakCommute (FullBeta (Var := Var)) (FullEta (Var := Var)) := by
  intro p q r hpq hqr
  obtain ⟨ s, hs1, hs2 ⟩ := postpone localPostpone_parBeta_fullEta (by
    convert hpq.mono _ |> Relation.ReflTransGen.trans <| hqr.mono _
    · exact fun a b hab => Or.inr hab
    · exact fun a b hab => Or.inl <| step_to_para hab)
  rw [parachain_iff_redex] at hs1
  exact ⟨s, hs1, hs2⟩

/-! ## Main theorem -/

theorem eta_beta_postpone {t t' t'' : Term Var}
    (htt' : t ↠ηᶠ t') (ht'' : Relation.TransGen FullBeta t' t'') :
    ∃ y, Relation.TransGen FullBeta t y ∧ y ↠ηᶠ t'' :=
  star_over_plus weakCommute_fullBeta_fullEta
    strongLocal_fullBeta_fullEta htt' ht''

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
