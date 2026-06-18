/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

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

variable {Var : Type u}

/-- The statement proved by induction: η postpones over a single parallel β-step
out of `M`. -/
public def TakaProp (M : Term Var) : Prop :=
  ∀ N P : Term Var, FullEta M N → Parallel N P → ∃ Q, Parallel M Q ∧ Q ↠ηᶠ P


variable [Infinite Var] [DecidableEq Var]

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
  · obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 ( by
      exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ) N0 _ he ‹_›
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
theorem parBeta_eta_redex {M1 M1' Z N1' : Term Var} (xs : Finset Var)
    (hLC : LC (Term.abs M1))
    (hbody : ∀ x ∉ xs, Parallel (M1 ^ fvar x) (M1' ^ fvar x))
    (hZN1' : Parallel Z N1') :
    Parallel (Term.app (Term.abs (Term.app (Term.abs M1) (Term.bvar 0))) Z) (M1' ^ N1') := by
  apply Parallel.beta xs _ hZN1'
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
  -- By `Infinite.exists_notMem_finset (ys2 ∪ xs ∪ fv A ∪ fv M1')`, pick a fresh variable `z`.
  obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ ys2 ∪ xs ∪ (fv A ∪ fv M1') := by
    exact Finset.exists_notMem _
  -- By `TakaProp`, we have `∃ W, ParBeta (A ^ fvar z) W ∧ FullEtaStar W (M1' ^ fvar z)`.
  obtain ⟨W, hWpar, hWeta⟩ : ∃ W, Parallel (openRec 0 (fvar z) A) W ∧ W ↠ηᶠ (openRec 0 (fvar z) M1') := by
    exact ih _ (by grind [size_openRec_fvar]) _ _ (hA _ (by grind)) (hbody _ (by grind))
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
    obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 ( by
      exact Nat.lt_succ_of_le ( Nat.le_add_right _ _ ) ) N0 _ he ‹_›
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
  have := ih ( M0 ^ fvar z ) ?_ ( N0 ^ fvar z ) ( M' ^ fvar z ) ?_ ?_;
  · exact exists_Q_abs z (by grind) (by grind) this.choose_spec.1 this.choose_spec.2
  · simp +decide [ Term.size ]
  · aesop
  · aesop

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
public theorem localPostpone_parBeta_fullEta :
    LocalPostpone (Parallel (Var := Var)) (FullEta (Var := Var)) :=
  fun _ _ _ he hp => eta_par_local _ _ _ he hp


/-
**η-postponement.** If `M` reduces to `N` under combined βη-reduction, then
there is an intermediate term `L` with `M ⟶β* L` and `L ⟶η* N`: every η-step can
be postponed past the β-steps.
-/
theorem eta_postponement {M N : Term Var} (h : Relation.ReflTransGen FullBetaEta M N) :
    ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  obtain ⟨L, hL₁, hL₂⟩ := postpone localPostpone_parBeta_fullEta (Relation.ReflTransGen.mono (fun a b hab => by
    cases hab <;> [exact Or.inl (step_to_para ‹_›); exact Or.inr ‹_›]) h)
  rw [parachain_iff_redex] at hL₁
  exact ⟨ L, hL₁, hL₂ ⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
