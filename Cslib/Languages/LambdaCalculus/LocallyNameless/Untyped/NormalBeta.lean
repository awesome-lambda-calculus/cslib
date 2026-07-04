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

variable {Var : Type u}


/-- Normal terms (locally closed β-normal forms): a variable head applied to a
spine of normal terms, possibly under abstractions.  A term in an application's
function position must not be an abstraction (otherwise there is a β-redex). -/
inductive Normal : Term Var → Prop where
  | fvar (x : Var) : Normal (fvar x)
  | app {M N : Term Var} :
      Normal M → (∀ C, M ≠ Term.abs C) → Normal N → Normal (app M N)
  | abs (xs : Finset Var) {M : Term Var} :
      (∀ x ∉ xs, Normal (M ^ fvar x)) → Normal (Term.abs M)

/-- A **NormalNotAbs** term is a normal term that is not an abstraction (a
variable-headed application spine). -/
def NormalNotAbs (M : Term Var) : Prop := Normal M ∧ ∀ C, M ≠ Term.abs C

theorem NormalNotAbs.fvar (x : Var) : NormalNotAbs (Term.fvar x : Term Var) :=
  ⟨Normal.fvar x, by rintro C ⟨⟩⟩

theorem NormalNotAbs.app {M N : Term Var} (hM : NormalNotAbs M) (hN : Normal N) :
    NormalNotAbs (Term.app M N) :=
  ⟨Normal.app hM.1 hM.2 hN, by rintro C ⟨⟩⟩

theorem NormalNotAbs.normal {M : Term Var} (h : NormalNotAbs M) : Normal M := h.1

/-
Normal terms are locally closed.
-/
@[grind ->]
theorem Normal.lc {M : Term Var} (h : Normal M) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ ih

theorem NormalNotAbs.lc {M : Term Var} (h : NormalNotAbs M) : LC M := h.1.lc

variable [DecidableEq Var] [HasFresh Var]

/-
Normal terms are β-normal forms.
-/
theorem Normal.betaNF {M : Term Var} (h : Normal M) : Relation.Normal FullBeta M := by
  induction h with
  | app _ _ _ _ _ =>
    intro  hu
    obtain ⟨ z, hz ⟩ := hu
    cases hz <;> grind
  | abs xs hM ih =>
    intro hN
    obtain ⟨ ys, hys ⟩ := hN
    cases hys with
    | base hys => cases hys
    | abs xs h => have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
                  apply ih x (by grind) ⟨_, (h x (by grind))⟩
  | fvar x => intro hM'
              obtain ⟨ N, hN ⟩ := hM'
              cases hN with | base hN => cases hN

/-
Normality is preserved by renaming a free variable to another.
-/
theorem Normal.subst_fvar {M : Term Var} (h : Normal M) (x y : Var) :
    Normal (M [x:=(Term.fvar y)]) := by
  revert h
  intro hM
  induction hM with
  | fvar z => rw [Term.subst_fvar]
              split <;> constructor
  | abs xs hM ih =>
    apply Normal.abs ( xs ∪ { x } )
    intro z hz
    convert ih z ( by aesop )
    rw  [Term.subst_open_var] <;> grind
  | app _ h₁ h₂ h₃ h₄ =>
    convert Normal.app h₃ _ h₄
    · rw [Term.subst_app]
    · intro C hC
      rename_i M _ _
      cases M with
      | fvar _ => rw [Term.subst_fvar] at hC
                  split at hC <;> cases hC
      | bvar _ => rw [Term.subst_bvar] at hC
                  cases hC
      | app _ _ =>  rw [Term.subst_app] at hC
                    cases hC
      | abs _ =>  rw [Term.subst_abs] at hC
                  grind

/-
Conversely, every locally closed β-normal form is normal.
-/
theorem betaNF_normal {N : Term Var} (hlc : LC N) (h : Relation.Normal FullBeta N) : Normal N := by
  induction hlc with
  | fvar x => exact Normal.fvar x
  | abs hN e _ ih =>
    apply Normal.abs ( hN ∪  e.fv )
    intro x hx
    apply ih x (by grind)
    intros g
    obtain ⟨t, g⟩ := g
    apply h
    exists (t^*x).abs
    apply Xi.abs e.fv
    intros y hy
    unfold close open'
    rw [close_openRec_to_subst]
    · have g := FullBeta.redex_subst_cong_lc _ _ (fvar y) x g (by grind)
      unfold open' at g
      rw [<- subst_intro_openRec] at g
      · exact g
      · grind
    · apply FullBeta.step_lc_r g
    · grind
  | app _ _ hN hM =>
    apply Normal.app
    · apply hN
      intro hu
      obtain ⟨ _, hu⟩ := hu
      apply h
      refine ⟨ _, Xi.appR (by assumption) hu⟩
    · intros C hC
      subst_vars
      apply h
      refine ⟨ _, Xi.base (Beta.beta (by assumption) (by assumption) )⟩
    · apply hM
      intro hu
      obtain ⟨ _, hu⟩ := hu
      apply h
      refine ⟨ _, Xi.appL (by assumption) hu⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
