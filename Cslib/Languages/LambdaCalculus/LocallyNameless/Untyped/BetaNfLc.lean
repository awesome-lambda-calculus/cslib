/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Foundations.Relation.Attr
public import Cslib.Foundations.Relation.Defs
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.BetaAt

/-! # Beta-normal forms in the locally nameless λ-calculus

This file defines `BetaNfLc`, the inductive predicate of locally-closed β-normal forms.
Its application constructor excludes abstractions in function position,
while its abstraction constructor checks the body after opening it with every fresh variable.

The file proves that `BetaNfLc` terms are locally closed and are normal with
respect to `FullBeta`, and that the predicate is preserved by free-variable
substitution. The converse theorem shows that every locally closed `FullBeta`
normal term satisfies `BetaNfLc`; together these results are stated as
`betaNF_iff`.
-/


@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}


/-- BetaNfLc terms (locally closed β-normal forms): a variable head applied to a
spine of normal terms, possibly under abstractions.  A term in an application's
function position must not be an abstraction (otherwise there is a β-redex). -/
inductive BetaNfLc : Term Var → Prop where
  | fvar (x : Var) : BetaNfLc (fvar x)
  | app {M N : Term Var} :
      BetaNfLc M → ¬ M.IsAbs  → BetaNfLc N → BetaNfLc (app M N)
  | abs (xs : Finset Var) {M : Term Var} :
      (∀ x ∉ xs, BetaNfLc (M ^ fvar x)) → BetaNfLc M.abs

abbrev BetaNfLcNotAbs (M : Term Var) : Prop := BetaNfLc M ∧ ¬ M.IsAbs

theorem BetaNfLcNotAbs.fvar (x : Var) : BetaNfLcNotAbs (Term.fvar x : Term Var) :=
  ⟨BetaNfLc.fvar x, by grind⟩

theorem BetaNfLcNotAbs.app {M N : Term Var} (hM : BetaNfLcNotAbs M) (hN : BetaNfLc N) :
    BetaNfLcNotAbs (Term.app M N) :=
  ⟨BetaNfLc.app hM.1 (by grind) hN, by grind⟩

theorem BetaNfLcNotAbs.normal {M : Term Var} (h : BetaNfLcNotAbs M) : BetaNfLc M := h.1

@[grind ->]
theorem BetaNfLc.lc {M : Term Var} (h : BetaNfLc M) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ ih

theorem BetaNfLcNotAbs.lc {M : Term Var} (h : BetaNfLcNotAbs M) : LC M := h.1.lc

variable [DecidableEq Var] [HasFresh Var]

theorem BetaNfLc.betaNF {M : Term Var} (h : BetaNfLc M) : Relation.Normal FullBeta M := by
  induction h with
  | fvar x =>
    rintro ⟨N, hN⟩
    cases hN with | base hN => cases hN
  | app _ _ _ _ _ =>
    rintro ⟨z, hz⟩
    cases hz <;> grind
  | abs xs hM ih =>
    rintro ⟨ys, hys⟩
    cases hys with
    | base hys => cases hys
    | abs xs h =>
        have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
        exact ih x (by grind) ⟨_, h x (by grind)⟩

theorem BetaNfLc.subst_fvar {M : Term Var} (h : BetaNfLc M) (x y : Var) :
    BetaNfLc (M[x:=Term.fvar y]) := by
  induction h with
  | fvar z =>
      rw [Term.subst_fvar]
      split <;> exact .fvar _
  | abs xs hM ih =>
    apply BetaNfLc.abs (xs ∪ { x }) (fun z hz => ?_)
    convert ih z (by grind)
    rw [Term.subst_open_var] <;> grind
  | app _ h₁ h₂ h₃ h₄ =>
    apply BetaNfLc.app h₃ (fun hC => ?_) h₄
    rw [isAbs_subst_fvar] at hC
    grind

theorem betaNF_normal {N : Term Var} (hlc : LC N) (h : Relation.Normal FullBeta N) :
  BetaNfLc N := by
  induction hlc with
  | fvar x => exact BetaNfLc.fvar x
  | abs hN e _ ih =>
    apply BetaNfLc.abs (hN ∪ e.fv)
      (fun x hx => ih x (by grind) (fun ⟨t, g⟩ => h ⟨(t^*x).abs, Xi.abs e.fv (fun y hy => ?_)⟩))
    rw [close_open_to_subst _ _ _ (FullBeta.step_lc_r g) (by grind)]
    have g := FullBeta.redex_subst_cong_lc _ _ (fvar y) x g (by grind)
    rwa [<- subst_intro_openRec (by grind)] at g
  | app m_lc n_lc hm hn =>
    refine .app (hm (fun ⟨ _, hu⟩ => h ⟨ _, .appR n_lc hu⟩)) (fun hC => h ?_)
                (hn (fun ⟨ _, hu⟩ => h ⟨ _, .appL m_lc hu⟩))
    cases hC
    exact ⟨_, Xi.base (Beta.beta m_lc n_lc)⟩

theorem betaNF_iff {N : Term Var} : LC N /\ Relation.Normal FullBeta N ↔ BetaNfLc N :=
  ⟨by grind [betaNF_normal], fun h => ⟨BetaNfLc.lc h, BetaNfLc.betaNF h⟩⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
