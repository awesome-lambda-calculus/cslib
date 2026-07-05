/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.NormalBeta
public import Cslib.Foundations.Relation.Confluence

/-!
# Parallel η-reduction and Takahashi's Lemma 3.7

This file formalises Takahashi's **parallel η-reduction** `⟹_η` (Definition 3.1
of "Parallel Reductions in λ-Calculus", *Information and Computation* 118 (1995),
120–127) in the locally nameless representation, together with **Lemma 3.7**:

  *If `P ⟹_η Q` and `P` is in β-normal form, then so is `Q`.*

The paper's Definition 3.1 reads
  * (η1) `x ⟹_η x`,
  * (η2) `λx.M ⟹_η λx.M'` if `M ⟹_η M'`,
  * (η3) `M N ⟹_η M' N'` if `M ⟹_η M'` and `N ⟹_η N'`,
  * (η4) `λz.M z ⟹_η M'` if `M ⟹_η M'` and `z ∉ FV(M)`.

In the locally nameless setting `z ∉ FV(M)` is expressed by requiring `M` to be
locally closed (so its body `app M (bvar 0)` uses the bound variable `bvar 0`
exactly once, at the tail, and `M` itself does not mention it).
-/


@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

/-- **Parallel η-reduction** `⟹_η` (Takahashi, Definition 3.1). -/
inductive ParEta : Term Var → Term Var → Prop
  /-- (η1) A free variable reduces to itself. -/
  | fvar (x : Var) : ParEta (fvar x) (fvar x)
  /-- (η3) Congruence for application. -/
  | app {M M' N N' : Term Var} :
      ParEta M M' → ParEta N N' → ParEta (app M N) (app M' N')
  /-- (η2) Congruence for abstraction (cofinite quantification). -/
  | abs (xs : Finset Var) {M M' : Term Var} :
      (∀ x ∉ xs, ParEta (M ^ fvar x) (M' ^ fvar x)) → ParEta (abs M) (abs M')
  /-- (η4) Parallel contraction of an η-redex `λz.M z ⟹_η M'`.  Local closure of
  `M` encodes `z ∉ FV(M)`. -/
  | eta {M M' : Term Var} :
      LC M → ParEta M M' → ParEta (abs (app M (bvar 0))) M'

/-- Parallel η-reduction is reflexive on locally closed terms. -/
@[scoped grind ->]
theorem ParEta.refl {M : Term Var} (h : LC M) : ParEta M M := by
  induction h with
  | fvar x => exact ParEta.fvar x
  | abs xs t _ ih => exact ParEta.abs xs ih
  | app _ _ ihM ihN => exact ParEta.app ihM ihN

theorem ParEta.fromFullEta {M N : Term Var} (h : M ⭢ηᶠ N) : ParEta M N := by
  induction h with
  | base h => cases h
              apply ParEta.eta <;> grind
  | appL _ _ _ => apply ParEta.app <;> grind
  | appR _ _ _ => apply ParEta.app <;> grind
  | abs xs _ ih => apply ParEta.abs xs ih

/-- Parallel η-reduction relates locally closed terms. -/
@[scoped grind ->]
theorem ParEta.regular [DecidableEq Var] [HasFresh Var]
  {M N : Term Var} (h : ParEta M N) : LC M ∧ LC N := by
  induction h with
  | fvar x => exact ⟨LC.fvar x, LC.fvar x⟩
  | app _ _ ihM ihN => exact ⟨LC.app ihM.1 ihN.1, LC.app ihM.2 ihN.2⟩
  | abs xs _ ih =>
      exact ⟨LC.abs xs _ fun x hx => (ih x hx).1, LC.abs xs _ fun x hx => (ih x hx).2⟩
  | @eta M M' hM _ ih =>
      refine ⟨LC.abs (∅ : Finset Var) _ fun x _ => ?_, ih.2⟩
      apply LC.app <;> grind

/-- A single parallel η-step is a sequence of full η-steps. -/
theorem ParEta.toFullEtaStar [DecidableEq Var] [HasFresh Var]
  {M N : Term Var} (h : ParEta M N) : M ↠ηᶠ N := by
  induction h with
  | fvar x => exact Relation.ReflTransGen.refl
  | @app M M' N N' hM hN ihM ihN =>
      exact Relation.ReflTransGen.trans (FullEta.redex_app_l_cong ihM ((ParEta.regular hN).1))
                                        (FullEta.redex_app_r_cong ihN ( (ParEta.regular hM).2))
  | abs xs h ih =>  apply FullEta.redex_abs_cong xs ih
                    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
                    specialize h x (by grind)
                    apply ParEta.regular at h
                    obtain ⟨hM, hM'⟩ := h
                    apply open_abs_lc hM
  | @eta M M' hM hMM' ih =>
      -- `λz.(M z) →η* λz.(M' z) →η M'`
  have hM' : LC M' := (ParEta.regular hMM').2
  have step1 : (Term.abs (Term.app M (Term.bvar 0))) ↠ηᶠ (Term.app M' (Term.bvar 0)).abs := by
    apply FullEta.redex_abs_cong (∅ : Finset Var)
    · intros x hx
      apply FullEta.redex_app_l_cong <;> grind
    · apply LC.abs ∅
      intro x hx
      grind
  exact step1.tail (Xi.base (Eta.eta hM'))

theorem paraEtachain_iff_redex [DecidableEq Var] [HasFresh Var]
  {M N : Term Var} : Relation.ReflTransGen ParEta M N ↔ M ↠ηᶠ N := by
  refine Iff.intro ?chain_redex ?redex_chain <;> intros h <;> induction h <;> try rfl
  case redex_chain redex chain => exact Relation.ReflTransGen.tail chain (ParEta.fromFullEta redex)
  case chain_redex para redex => exact Relation.ReflTransGen.trans redex (ParEta.toFullEtaStar para)

/-!
# `k`-fold η-expansion and the structure of η-expansions of β-normal forms

This file develops the machinery behind Takahashi's Lemma 3.6.  The central
notion is the **`k`-fold η-expansion** `etaExp M k`, written `(M)_k` in the
paper: `(M)_0 = M` and `(M)_{k+1} = λz. ((M)_k z)`.

The main export is `etaExpand_hasBetaNF`: an η-expansion `L ↠η N` of a β-normal
form `N` has a β-normal form.
-/

/-- `k`-fold η-expansion: `(M)_0 = M`, `(M)_{k+1} = λz.((M)_k z)`.

In the locally nameless representation `λz.(P z)` with `P` locally closed is
`abs (app P (bvar 0))`. -/
@[scoped grind =]
def etaExp (M : Term Var) : ℕ → Term Var
  | 0 => M
  | (k + 1) => abs (app (etaExp M k) (bvar 0))

@[simp] theorem etaExp_zero (M : Term Var) : etaExp M 0 = M := rfl

@[simp] theorem etaExp_succ (M : Term Var) (k : ℕ) :
    etaExp M (k + 1) = abs (app (etaExp M k) (bvar 0)) := rfl

/-- The `k`-fold η-expansion of a locally closed term is locally closed. -/
theorem etaExp_lc [DecidableEq Var] [HasFresh Var]
  {M : Term Var} (hM : LC M) (k : ℕ) : LC (etaExp M k) := by
  induction k with
  | zero => exact hM
  | succ k ih =>
      refine LC.abs (∅ : Finset Var) _ (fun x _ => (LC.app ?_ ?_))
      all_goals grind

/-- The `k`-fold η-expansion η-reduces back to the original term. -/
theorem etaExp_fullEtaStar [DecidableEq Var] [HasFresh Var]
  {M : Term Var} (hM : LC M) (k : ℕ) :
    (etaExp M k) ↠ηᶠ M := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>  convert Relation.ReflTransGen.head ( Xi.base ( Eta.eta ( etaExp_lc hM n ) ) ) ih
                  grind

/-- Layers of η-expansion compose. -/
theorem etaExp_add (M : Term Var) (a b : ℕ) :
    etaExp M (a + b) = etaExp (etaExp M b) a := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]

/-! ## Collapse lemmas for η-expansion towers -/

/-
Congruence: β-reducing the base β-reduces the whole tower.
-/
theorem etaExp_betaStar_congr [DecidableEq Var] [HasFresh Var]
  {M M' : Term Var} (hM : LC M)
    (h : M ↠βᶠ M') (k : ℕ) :
    (etaExp M k) ↠βᶠ (etaExp M' k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    apply FullBeta.redex_abs_cong ( ∅ : Finset Var )
    intro x hx
    convert FullBeta.redex_app_l_cong ih (LC.fvar x)
    · grind [etaExp_lc hM k]
    · apply FullBeta.steps_lc_or_rfl at ih
      grind [etaExp_lc]

/-
A tower of η-expansions over an **abstraction** β-collapses completely back
to the abstraction (each created redex `(λx.C) z →β C[z]` undoes one layer).
-/
theorem etaExp_abs_collapse [DecidableEq Var] [HasFresh Var]
  {C : Term Var} (hC : LC (Term.abs C)) (k : ℕ) :
    (etaExp (Term.abs C) k) ↠βᶠ (Term.abs C) := by
  have h_beta : FullBeta (abs (app (abs C) (bvar 0))) (abs C) := by
    obtain ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
    apply Xi.abs { x }
    intro y hy
    convert Xi.base ( Beta.beta ( show LC ( abs C ) from hC ) ( show LC ( fvar y ) from LC.fvar y))
    grind
  induction k with
  | zero =>  exact .refl
  | succ k ih =>
    have h_congr : (abs (app (etaExp C.abs k) (bvar 0))) ↠βᶠ (abs (app (abs C) (bvar 0))) := by
      apply FullBeta.redex_abs_cong ∅
      intro x hx
      convert FullBeta.redex_app_l_cong ih (LC.fvar x)
      · apply FullBeta.steps_lc_or_rfl at ih
        cases ih with grind
      · grind
    exact h_congr.tail h_beta

/-
When an η-expansion tower is **applied** to an argument, all layers
β-collapse (linearly, no duplication): `(B)_k G ↠β B G`.
-/
theorem etaExp_app_collapse [DecidableEq Var] [HasFresh Var]
  {B G : Term Var} (hB : LC B) (hG : LC G) (k : ℕ) :
    (app (etaExp B k) G) ↠βᶠ (app B G) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    refine Relation.ReflTransGen.head ?_ ih
    convert Xi.base ( Beta.beta ( etaExp_lc hB ( k + 1 ) ) hG )
    · grind
    · unfold open' openRec
      apply congr
      · apply congr rfl
        rw [open_lc]
        apply FullBeta.steps_lc_or_rfl at ih
        cases ih with
        | inl h =>  obtain ⟨h, _⟩ := h
                    cases h
                    grind
        | inr h => grind
      · grind


/-! ## Normal forms of η-expansion towers -/

/-
`(B)_1` of a NormalNotAbs base `B` is normal.
-/
theorem Normal.etaExp_one [DecidableEq Var] [HasFresh Var]
  {B : Term Var} (hne : NormalNotAbs B) :
    Normal (etaExp B 1) := by
  apply Normal.abs ∅
  intro x hx
  convert Normal.app hne.1 hne.2 ( Normal.fvar x )
  grind [NormalNotAbs.lc hne]

/-
A tower of η-expansions over a **NormalNotAbs** base has a normal (β-nf) form:
it β-collapses to `(B)_1` (or to `B` itself when `k = 0`).
-/
theorem etaExp_NormalNotAbs_normalForm [DecidableEq Var] [HasFresh Var]
  {B : Term Var} (hne : NormalNotAbs B) (k : ℕ) :
    ∃ M, (etaExp B k) ↠βᶠ M ∧ Normal M := by
  -- If k = 0, we can take M = B.
  by_cases hk : k = 0
  · exact ⟨ B, by subst hk; exact Relation.ReflTransGen.refl, hne.1 ⟩
  · obtain ⟨ k, rfl ⟩ := Nat.exists_eq_succ_of_ne_zero hk
    clear hk
    exists (B.app (bvar 0)).abs
    induction k with unfold etaExp
    | zero => exact ⟨Relation.ReflTransGen.refl, Normal.etaExp_one hne⟩
    | succ n h =>
      obtain ⟨ h1, h2 ⟩ := h
      constructor
      · apply FullBeta.redex_abs_cong ∅
        intros x hx
        unfold open' openRec
        apply NormalNotAbs.lc at hne
        rw [open_lc _ _ B hne, open_lc _ _ (B.etaExp (n+1)) (etaExp_lc hne _)]
        apply etaExp_app_collapse <;> grind
      · grind

/-! ## Structure of a single parallel η-step (Takahashi's Lemma 3.2) -/

/-- A tower `(Y)_k` reduces to `Z` in a single parallel η-step whenever `Y ⟹η Z`. -/
theorem parEta_etaExp [DecidableEq Var] [HasFresh Var]
  {Y Z : Term Var} (h : ParEta Y Z) (k : ℕ) :
    ParEta (etaExp Y k) Z := by
  induction k with
  | zero => exact h
  | succ k ih => exact ParEta.eta (etaExp_lc (ParEta.regular h).1 k) ih

/-- Parallel β-reduction lifts through η-expansion towers. -/
theorem parBeta_etaExp_congr [DecidableEq Var] [HasFresh Var]
  {A A' : Term Var} (h : Parallel A A') (k : ℕ) :
    Parallel (etaExp A k) (etaExp A' k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
      refine Parallel.abs (∅ : Finset Var) (fun x _ => ?_)
      grind

/-
**Lemma 3.2 (variable case).**  A single parallel η-reduct that is a variable
comes from a `k`-fold η-expansion of that variable.
-/
theorem parEta_inv_fvar {L : Term Var} {x : Var}
    (h : ParEta L (fvar x)) : ∃ k, L = etaExp (fvar x) k := by
  generalize hy : fvar x = y
  rw [hy] at h
  induction h with
  | fvar x => exists 0
  | app _ _ _ _ => grind
  | abs xs _ _ => grind
  | eta _ _ ih => specialize ih hy
                  obtain ⟨ k, rfl ⟩ := ih
                  exact ⟨ k + 1, rfl ⟩

/-
**Lemma 3.2 (application case).**
-/
theorem parEta_inv_app {L A B : Term Var}
    (h : ParEta L (app A B)) :
    ∃ k A' B', L = etaExp (app A' B') k ∧ ParEta A' A ∧ ParEta B' B := by
  revert h
  induction n : Term.size L using Nat.strong_induction_on generalizing L A B with
  | h n ih=>
  rintro ( h | h | h | h )
  · exact ⟨ 0, _, _, rfl, h, by assumption ⟩
  · rename_i M hM
    obtain ⟨ k, A', B', rfl, hA', hB' ⟩ := ih _ ( by
      simp +decide [ ← n, Term.size ]
      grind +splitImp ) rfl hM
    exact ⟨ k + 1, A', B', rfl, hA', hB' ⟩

/-
**Lemma 3.2 (abstraction case).**
-/
theorem parEta_inv_abs {L A : Term Var}
    (h : ParEta L (Term.abs A)) :
    ∃ (k : ℕ) (A' : Term Var) (xs : Finset Var), L = etaExp (Term.abs A') k ∧
      ∀ x ∉ xs, ParEta (A' ^ fvar x) (A ^ fvar x) := by
  revert h
  induction n : Term.size L using Nat.strong_induction_on generalizing L A with
  | h n ih =>
  rintro ( h | h | h | h )
  · exact ⟨ 0, _, h, rfl, by assumption ⟩
  · rename_i M hM
    obtain ⟨ k, A', xs, rfl, hA' ⟩ := ih _ ( by
      simp +decide [ ← n, Term.size ]
      linarith ) rfl hM
    exact ⟨ k + 1, A', xs, rfl, hA' ⟩

variable [DecidableEq Var] [HasFresh Var]

/-! ## The reconstruction (core of Lemma 3.6) -/

/-- **Core reconstruction.**  If `A` is normal and `L ⟹η A` (a single parallel
η-step), then `L` β-reduces to a normal form; moreover if `A` is NormalNotAbs, `L`
β-reduces to a tower `(B)_k` over a NormalNotAbs base `B`. -/
theorem core_par {A : Term Var} (hA : Normal A) : ∀ L, ParEta L A →
    (∃ M, L ↠βᶠ M ∧ Normal M) ∧
    (NormalNotAbs A → ∃ k B, L ↠βᶠ (etaExp B k) ∧ NormalNotAbs B) := by
  induction hA with
  | fvar x =>
      intro L hL
      obtain ⟨k, rfl⟩ := parEta_inv_fvar hL
      exact ⟨etaExp_NormalNotAbs_normalForm (NormalNotAbs.fvar x) k,
        fun _ => ⟨k, Term.fvar x, Relation.ReflTransGen.refl, NormalNotAbs.fvar x⟩⟩
  | @app M N hM hMne hN ihM ihN =>
      intro L hL
      obtain ⟨j, M', N', rfl, hM', hN'⟩ := parEta_inv_app hL
      have lcM' : LC M' := (ParEta.regular hM').1
      have lcN' : LC N' := (ParEta.regular hN').1
      obtain ⟨k1, B1, hB1red, hB1neu⟩ := (ihM M' hM').2 ⟨hM, hMne⟩
      obtain ⟨Nhat, hNred, hNnorm⟩ := (ihN N' hN').1
      have hcollapse : (app M' N') ↠βᶠ (app B1 Nhat) :=
        (FullBeta.redex_app_l_cong hB1red lcN').trans
          ((FullBeta.redex_app_r_cong  hNred (etaExp_lc (NormalNotAbs.lc hB1neu) k1)).trans
            (etaExp_app_collapse (NormalNotAbs.lc hB1neu) (Normal.lc hNnorm) k1))
      have hBneu : NormalNotAbs (app B1 Nhat) := NormalNotAbs.app hB1neu hNnorm
      have hcongr : (etaExp (app M' N') j) ↠βᶠ (etaExp (app B1 Nhat) j) :=
        etaExp_betaStar_congr (LC.app lcM' lcN') hcollapse j
      obtain ⟨M2, h2red, h2norm⟩ := etaExp_NormalNotAbs_normalForm hBneu j
      refine ⟨⟨M2, hcongr.trans h2red, h2norm⟩, fun _ => ⟨j, app B1 Nhat, hcongr, hBneu⟩⟩
  | @abs xs body hbody ihbody =>
      intro L hL
      obtain ⟨j, body', xs2, rfl, hred⟩ := parEta_inv_abs hL
      obtain ⟨x0, hx0⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨C0, hC0red, hC0norm⟩ :=
        (ihbody x0 (by grind) (body' ^ fvar x0) (hred x0 (by grind))).1
      set D := closeRec 0 x0 C0 with hDdef
      have hDred : ∀ x : Var, (body' ^ fvar x) ↠βᶠ (D ^ fvar x) := by
        intro x
        have e1 : body' ^ fvar x = Term.subst (body' ^ fvar x0) x0 (fvar x) :=
          by rw [Term.subst_intro x0] <;> grind
        have e2 : (D : Term Var) ^ fvar x = Term.subst C0 x0 (fvar x) :=
          by  rw [hDdef]
              unfold open'
              rw [close_openRec_to_subst] <;> grind
        rw [e1, e2]
        exact FullBeta.redex_subst_cong_ls _ _ _ _ hC0red (LC.fvar x)
      have hDnormal : Normal (Term.abs D) := by
        refine Normal.abs (∅ : Finset Var) (fun x _ => ?_)
        have e2 : (D : Term Var) ^ fvar x = Term.subst C0 x0 (fvar x) :=
          by  rw [hDdef]
              unfold open'
              rw [close_openRec_to_subst] <;> grind
        rw [e2]; exact Normal.subst_fvar hC0norm x0 x
      have hDabs : (Term.abs body') ↠βᶠ (Term.abs D) :=
        FullBeta.redex_abs_cong (∅ : Finset Var) (fun x _ => hDred x)
      have lcAbsBody' : LC (Term.abs body') :=
        LC.abs xs2 body' (fun x hx => (ParEta.regular (hred x hx)).1)
      refine ⟨⟨Term.abs D,
        (etaExp_betaStar_congr lcAbsBody' hDabs j).trans
          (etaExp_abs_collapse (Normal.lc hDnormal) j), hDnormal⟩, ?_⟩
      rintro ⟨-, hc⟩
      exact absurd rfl (hc body)

/-
Substitutivity of parallel η-reduction.
-/
theorem ParEta.subst_par {A A' B B' : Term Var} (z : Var)
    (hA : ParEta A A') (hB : ParEta B B') :
    ParEta (Term.subst A z B) (Term.subst A' z B') := by
  induction hA generalizing B B' with
  | fvar x => unfold Term.subst
              split_ifs <;> [ exact hB; exact ParEta.fvar _ ]
  | app _ _ _ _ => exact ParEta.app ( by aesop ) ( by aesop )
  | abs xs h ih => exact ParEta.abs ( xs ∪ { z } ) fun x hx => by
                      grind +suggestions
  | eta hM hMM' ih => exact ParEta.eta ( Term.subst_lc hM hB.regular.1 ) ( ih hB )

/-
Opening congruence for parallel η-reduction.
-/
theorem ParEta.open_par {M M' N N' : Term Var} (xs : Finset Var)
    (hbody : ∀ x ∉ xs, ParEta (M ^ Term.fvar x) (M' ^ Term.fvar x))
    (hN : ParEta N N') :
    ParEta (M ^ N) (M' ^ N') := by
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  convert ParEta.subst_par z ( hbody z (by grind) ) hN
  · rw [ Term.subst_intro z] <;> grind
  · rw [ Term.subst_intro z] <;> grind

/-
Applying a `j`-fold η-expansion of an abstraction to an argument parallel
β-reduces (in one step) to the contracted redex: `((λx.C)_j) Z ⟹β C'[Z']`.
-/
theorem parBeta_etaExp_abs_app {C C' Z Z' : Term Var} (xs : Finset Var)
    (hbody : ∀ x ∉ xs, Parallel (C ^ fvar x) (C' ^ fvar x)) (hZ : Parallel Z Z')
    (j : ℕ) :
    Parallel (Term.app (etaExp (Term.abs C) j) Z) (C' ^ Z') := by
  revert hbody hZ
  induction j generalizing C C' Z Z' xs with
  | zero =>
    intro hbody hZ
    apply Parallel.beta xs hbody hZ
  | succ j ih =>
    intro hbody hZ
    have hCabs : LC (Term.abs C) := by
      have hLC : ∀ x ∉ xs, LC (C ^ fvar x) := by grind
      apply LC.abs
      exact hLC
    apply Parallel.beta xs
    · intro x hx
      convert ih xs hbody ( Parallel.fvar x )
      grind [etaExp_lc hCabs j]
    · assumption

/-! ## Parallel η/β postponement (Takahashi's Lemma 3.4) -/

/-
**Lemma 3.4.**  A parallel η-step postpones over a parallel β-step:
`M ⟹η P ⟹β N` implies `M ⟹β P' ⟹η N` for some `P'`.
-/
theorem parEta_parBeta_postpone : LocalPostpone (Parallel (Var := Var)) ParEta := by
  intros M N P hη hβ
  revert hη
  induction hβ generalizing M with
  | fvar x =>  grind +suggestions
  | app _ _ ih1 ih2 =>
    intro hM
    obtain ⟨ k, M1, M2, rfl, hM1, hM2 ⟩ := parEta_inv_app hM
    obtain ⟨ P1, hP1, hP1' ⟩ := ih1 hM1
    obtain ⟨ P2, hP2, hP2' ⟩ := ih2 hM2
    use etaExp (app P1 P2) k
    exact ⟨parBeta_etaExp_congr (Parallel.app hP1 hP2) k, parEta_etaExp (ParEta.app hP1' hP2') k⟩
  | abs xs hβ ih =>
    rename_i xs M M'
    intro hM
    obtain ⟨ k, M0, xs2, rfl, hM0 ⟩ := parEta_inv_abs hM
    obtain ⟨x0, hx0⟩ := fresh_exists <| free_union [fv] Var
    obtain ⟨ Q0, hQ0 ⟩ := ih x0 ( by aesop ) ( hM0 x0 ( by aesop ) )
    -- Set `M0' = closeRec 0 x0 Q0`.
    set M0' : Term Var := closeRec 0 x0 Q0
    -- Prove the cofinite families for all `x` (using `LC Q0 = (ParBeta.regular ‹ParBeta (M0^x0) Q0›).2`, `subst_intro` with `x0∉fv M0`, `x0∉fv M'`, and `open_close_lc`):
    have h_cofinite : ∀ x ∉ xs ∪ xs2, Parallel (M0 ^ fvar x) (M0' ^ fvar x) ∧ ParEta (M0' ^ fvar x) (M' ^ fvar x) := by
      intro x hx
      have h_subst : M0 ^ fvar x = Term.subst (M0 ^ fvar x0) x0 (fvar x)  := by
        apply Term.subst_intro
        grind
      have h_subst' : M0' ^ fvar x = Term.subst Q0 x0 (fvar x) := by
        unfold open'
        rw [close_openRec_to_subst] <;> grind
      have h_subst'' : M' ^ fvar x = Term.subst (M' ^ fvar x0) x0 (fvar x)  := by
        apply Term.subst_intro
        grind
      constructor
      · rw [ h_subst, h_subst' ]
        apply para_subst <;> grind
      · rw [h_subst', h_subst'']; exact ParEta.subst_par x0 hQ0.2 (ParEta.fvar x)
    refine ⟨ etaExp M0'.abs k, ?_, ?_ ⟩
    · apply parBeta_etaExp_congr
      apply Parallel.abs
      exact fun x hx => h_cofinite x hx |>.1
    · apply parEta_etaExp
      apply ParEta.abs
      exact fun x hx => h_cofinite x hx |>.2
  | beta xs h₁ h₂ h₃ h₄ =>
    intro hη
    rename_i xs M' N' M'' N''
    obtain ⟨ k, M₁, M₂, rfl, hM₁, hM₂ ⟩ := parEta_inv_app hη
    obtain ⟨ j, M₁b, xs', rfl, hM₁b ⟩ := parEta_inv_abs hM₁
    obtain ⟨x0, hx0'⟩ := fresh_exists <| free_union [fv] Var
    obtain ⟨ Q₁, hQ₁, hQ₂ ⟩ := h₃ x0 (by grind) ( hM₁b x0 (by grind))
    -- Set `M₁b' = closeRec 0 x0 Q₁`.
    set M₁b' : Term Var := closeRec 0 x0 Q₁
    -- Prove the cofinite families for all `x` (using `LC Q₁ = (ParBeta.regular ‹ParBeta (M₁b^x0) Q₁›).2`, `subst_intro` with `x0∉fv M₁b`, `x0∉fv N'`, and `open_close_lc`):
    have hM₁b'_family : ∀ x ∉ xs ∪ xs', Parallel (M₁b ^ fvar x) (M₁b' ^ fvar x) := by
      intro x hx
      convert para_subst x0 hQ₁ ( Parallel.fvar x )
      · rw [ Term.subst_intro ]
        grind
      · unfold open'
        rw [close_openRec_to_subst] <;> grind
    have hM₁b'_family' : ∀ x ∉ xs ∪ xs', ParEta (M₁b' ^ fvar x) (N' ^ fvar x) := by
      intro x hx
      convert ParEta.subst_par x0 hQ₂ ( ParEta.fvar x ) using 1
      · unfold open'
        rw [close_openRec_to_subst] <;> grind
      · rw [ Term.subst_intro x0 _ _ (by grind)]
        rw [subst_open] <;> grind
    obtain ⟨ P', hP', hP'' ⟩ := h₄ hM₂
    refine ⟨ etaExp ( M₁b' ^ P' ) k, ?_, parEta_etaExp ?_ k ⟩
    · convert parBeta_etaExp_congr ( parBeta_etaExp_abs_app ( xs ∪ xs' ) hM₁b'_family hP' j ) k
    · apply ParEta.open_par
      · exact hM₁b'_family'
      · exact hP''


/-!
# Takahashi's Lemma 3.6

This file assembles **Lemma 3.6** of Takahashi, *Parallel Reductions in
λ-Calculus*, *Information and Computation* 118 (1995), 120–127:

  *If `P ⟹_η Q` (parallel η-reduction) and `Q` has a β-normal form, then `P` has
  a β-normal form.*

Here "`X` has a β-normal form" (`HasBetaNF X`, defined in `EtaExpand`) means that
some β-reduction of `X` reaches a β-normal form, i.e. `∃ N, X ↠β N ∧ BetaNF N`.

The proof follows Takahashi:

* `Q` has a β-normal form `N`, and `N` is *normal* (`betaNF_normal`).
* By parallel η/β **postponement** (Lemma 3.4, `parEta_parBetaStar_postpone`),
  the reduction `P ⟹η Q ⟹β* N` reorganises to `P ⟹β* P' ⟹η N`.
* By the **core reconstruction** (`core_par`, built on the structure of a single
  parallel η-step, Lemma 3.2), the η-expansion `P' ⟹η N` of the normal form `N`
  has a β-normal form; combining with `P ↠β P'` gives one for `P`.
-/


/-- **Takahashi's Lemma 3.6.**  If `P ⟹_η Q` (parallel η-reduction) and `Q` has a
β-normal form, then `P` has a β-normal form. -/
theorem parEta_hasBetaNF {P Q : Term Var}
    (h : ParEta P Q) (hQ : Relation.Normalizable FullBeta Q) :
                           Relation.Normalizable FullBeta P := by
  obtain ⟨N, hQN, hN⟩ := hQ
  -- `N` is the β-normal form of `Q`; it is locally closed and hence `Normal`.
  have hNlc : LC N := by  apply FullBeta.steps_lc_or_rfl at hQN
                          cases hQN with
                          | inl _ => grind
                          | inr hQN =>  subst Q
                                        apply ParEta.regular at h
                                        grind
  rw [<- parachain_iff_redex] at hQN
  -- LocalPostpone the η-step past all β-steps: `P ⟹β* P' ⟹η N`.
  obtain ⟨P', hPP', hP'N⟩ := postpone_a parEta_parBeta_postpone h hQN
  -- The η-expansion `P' ⟹η N` of the normal form `N` has a β-normal form.
  obtain ⟨M, hP'M, hMnorm⟩ := (core_par (betaNF_normal hNlc hN) P' hP'N).1
  rw [parachain_iff_redex] at hPP'
  apply  Normal.betaNF at hMnorm
  exact ⟨M, .trans hPP' hP'M, hMnorm⟩


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
