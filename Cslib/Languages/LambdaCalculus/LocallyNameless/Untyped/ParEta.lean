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
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Takahashi
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Abstract

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

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]



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

/-- Opening the η-redex body `app M (bvar 0)` of a locally closed `M`. -/
theorem open_app_bvar_lc {M : Term Var} (hM : LC M) (x : Var) :
    (Term.app M (Term.bvar 0)) ^ Term.fvar x = Term.app M (Term.fvar x) := by
  show Term.app (openRec 0 (Term.fvar x) M) (openRec 0 (Term.fvar x) (Term.bvar 0)) = _
  grind

/-- Any transitive-closure reduction has a first step. -/
theorem exists_first_step {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) : ∃ c, r a c := by
  induction h with
  | single hab => exact ⟨_, hab⟩
  | tail _ _ ih => exact ih

/-- Parallel η-reduction relates locally closed terms. -/
@[scoped grind]
theorem ParEta.regular {M N : Term Var} (h : ParEta M N) : LC M ∧ LC N := by
  induction h with
  | fvar x => exact ⟨LC.fvar x, LC.fvar x⟩
  | app _ _ ihM ihN => exact ⟨LC.app ihM.1 ihN.1, LC.app ihM.2 ihN.2⟩
  | abs xs _ ih =>
      exact ⟨LC.abs xs _ fun x hx => (ih x hx).1, LC.abs xs _ fun x hx => (ih x hx).2⟩
  | @eta M M' hM _ ih =>
      refine ⟨LC.abs (∅ : Finset Var) _ fun x _ => ?_, ih.2⟩
      rw [open_app_bvar_lc hM]
      exact LC.app hM (LC.fvar x)

/-- Parallel η-reduction is reflexive on locally closed terms. -/
@[scoped grind]
theorem ParEta.refl {M : Term Var} (h : LC M) : ParEta M M := by
  induction h with
  | fvar x => exact ParEta.fvar x
  | abs xs t _ ih => exact ParEta.abs xs ih
  | app _ _ ihM ihN => exact ParEta.app ihM ihN

/-- A single parallel η-step is a sequence of full η-steps. -/
theorem ParEta.toFullEtaStar {M N : Term Var} (h : ParEta M N) : M ↠ηᶠ N := by
  induction h with
  | fvar x => exact Relation.ReflTransGen.refl
  | @app M M' N N' hM hN ihM ihN =>
      apply Relation.ReflTransGen.trans
      · exact (FullEta.redex_app_l_cong ihM ( (ParEta.regular hN).1))
      · exact (FullEta.redex_app_r_cong ihN ( (ParEta.regular hM).2))
  | abs xs h ih =>  apply FullEta.redex_abs_cong xs ih
                    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
                    specialize h x (by grind)
                    apply ParEta.regular at h
                    obtain ⟨hM, hM'⟩ := h
                    apply open_abs_lc hM
  | @eta M M' hM hMM' ih =>
      -- `λz.(M z) →η* λz.(M' z) →η M'`
  have hM' : LC M' := (ParEta.regular hMM').2
  have step1 : (Term.abs (Term.app M (Term.bvar 0))) ↠ηᶠ (Term.abs (Term.app M' (Term.bvar 0))) := by
    apply FullEta.redex_abs_cong (∅ : Finset Var)
    · intros x hx
      rw [open_app_bvar_lc hM, open_app_bvar_lc hM']
      apply FullEta.redex_app_l_cong ih (by grind)
    · apply LC.abs ∅
      intro x hx
      grind
  exact step1.tail (Xi.base (Eta.eta hM'))

theorem ParEta.fromFullEta {M N : Term Var} (h : M ⭢ηᶠ N) : ParEta M N := by
  induction h with
  | base h => cases h
              apply ParEta.eta <;> grind
  | appL _ _ _ => apply ParEta.app <;> grind
  | appR _ _ _ => apply ParEta.app <;> grind
  | abs xs _ ih => apply ParEta.abs xs ih

theorem paraEtachain_iff_redex {M N : Term Var} : Relation.ReflTransGen ParEta M N ↔ M ↠ηᶠ N := by
  refine Iff.intro ?chain_redex ?redex_chain <;> intros h <;> induction h <;> try rfl
  case redex_chain redex chain => exact Relation.ReflTransGen.tail chain (ParEta.fromFullEta redex)
  case chain_redex para  redex => exact Relation.ReflTransGen.trans redex (ParEta.toFullEtaStar para)

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
theorem etaExp_lc {M : Term Var} (hM : LC M) (k : ℕ) : LC (etaExp M k) := by
  induction k with
  | zero => exact hM
  | succ k ih =>
      refine LC.abs (∅ : Finset Var) _ (fun x _ => ?_)
      rw [open_app_bvar_lc ih]
      exact LC.app ih (LC.fvar x)

/-- The `k`-fold η-expansion η-reduces back to the original term. -/
theorem etaExp_fullEtaStar {M : Term Var} (hM : LC M) (k : ℕ) :
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

/-! ## β-reduction congruences (reflexive-transitive) -/

/-- Local closure is preserved by β-reduction (reflexive-transitive). -/
theorem FullBetaStar.lc_right {M N : Term Var} (hM : LC M) (h : M ↠βᶠ N) :
    LC N := by
  induction h with
  | refl => exact hM
  | tail h step ih => apply FullBeta.step_lc_r step

/-- Local closure is preserved by η-reduction (reflexive-transitive). -/
theorem FullEtaStar.lc_right {M N : Term Var} (hM : LC M) (h : M ↠ηᶠ N) :
    LC N := by
  induction h with
  | refl => exact hM
  | tail _ step ih => exact FullEta.step_lc_r step

/-- If `a ↠η b` and `b` is locally closed, then so is `a` (every η-step relates
locally closed terms). -/
theorem FullEtaStar.lc_left {a b : Term Var} (hb : LC b) (h : a ↠ηᶠ b) :
    LC a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head step _ _ => exact FullEta.step_lc_l step

/-- Substitutivity of β-star. -/
theorem FullBetaStar.subst {A B : Term Var} (h : A ↠βᶠ B) (x : Var)
    {u : Term Var} (hu : LC u) :
    (Term.subst x u A) ↠βᶠ (Term.subst x u B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail (FullBeta.subst step x hu)

/-- Abstraction congruence for β-star. -/
theorem FullBetaStar.abs {M M' : Term Var} (xs : Finset Var)
    (h : ∀ x ∉ xs, (M ^ fvar x) ↠βᶠ (M' ^ fvar x)) :
    (Term.abs M) ↠βᶠ (Term.abs M') :=
  XiStar.abs (fun _ _ => Beta.regular)
    (fun _ _ hab y _w hw => Beta.subst hab y hw) xs h

/-- Left-application congruence for β-star. -/
theorem FullBetaStar.appL {Z M N : Term Var} (hZ : LC Z) (h : M ↠βᶠ N) :
    (app Z M) ↠βᶠ (app Z N) :=
  XiStar.appL hZ h

/-- Right-application congruence for β-star. -/
theorem FullBetaStar.appR {Z M N : Term Var} (hZ : LC Z) (h : M ↠βᶠ N) :
    (app M Z) ↠βᶠ (app N Z) :=
  XiStar.appR hZ h

/-! ## Collapse lemmas for η-expansion towers -/

/-
Congruence: β-reducing the base β-reduces the whole tower.
-/
theorem etaExp_betaStar_congr {M M' : Term Var} (hM : LC M)
    (h : M ↠βᶠ M') (k : ℕ) :
    (etaExp M k) ↠βᶠ (etaExp M' k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    apply FullBetaStar.abs ( ∅ : Finset Var )
    intro x hx
    convert FullBetaStar.appR ( LC.fvar x ) ih
    · rw [ open_app_bvar_lc ( etaExp_lc hM k ) ]
    · exact open_app_bvar_lc ( etaExp_lc ( FullBetaStar.lc_right hM h ) k ) x

/-
A tower of η-expansions over an **abstraction** β-collapses completely back
to the abstraction (each created redex `(λx.C) z →β C[z]` undoes one layer).
-/
theorem etaExp_abs_collapse {C : Term Var} (hC : LC (Term.abs C)) (k : ℕ) :
    (etaExp (Term.abs C) k) ↠βᶠ (Term.abs C) := by
  -- By definition of `FullBetaStar`, we know that `FullBetaStar (abs (app (abs C) (bvar 0))) (abs C)`.
  have h_beta : FullBeta (abs (app (abs C) (bvar 0))) (abs C) := by
    obtain ⟨x, hx⟩ : ∃ x : Var, x ∉ fv C := by
      exact Set.Finite.exists_notMem ( C.fv.finite_toSet );
    apply Xi.abs { x }
    intro y hy;
    convert Xi.base ( Beta.beta ( show LC ( abs C ) from hC ) ( show LC ( fvar y ) from LC.fvar y ) )
    convert open_app_bvar_lc hC y using 1;
  induction k with
  | zero =>  exact .refl
  | succ k ih =>
    have h_congr : (abs (app (etaExp C.abs k) (bvar 0))) ↠βᶠ (abs (app (abs C) (bvar 0))) := by
      apply FullBetaStar.abs ∅;
      intro x hx;
      convert FullBetaStar.appR ( LC.fvar x ) ( ih ) using 1;
      · rw [ open_app_bvar_lc ]
        apply FullBeta.steps_lc_or_rfl at ih
        cases ih with grind
      · convert open_app_bvar_lc _ x;
        exact hC;
    exact h_congr.tail h_beta

/-
When an η-expansion tower is **applied** to an argument, all layers
β-collapse (linearly, no duplication): `(B)_k G ↠β B G`.
-/
theorem etaExp_app_collapse {B G : Term Var} (hB : LC B) (hG : LC G) (k : ℕ) :
    (app (etaExp B k) G) ↠βᶠ (app B G) := by
  induction k with
  | zero => exact .refl;
  | succ k ih =>
    refine Relation.ReflTransGen.head ?_ ih
    convert Xi.base ( Beta.beta ( etaExp_lc hB ( k + 1 ) ) hG ) using 1
    grind
    unfold open' openRec
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

/-! ## Neutral and normal terms (the structure of β-normal forms) -/

/-- Normal terms (locally closed β-normal forms): a variable head applied to a
spine of normal terms, possibly under abstractions.  A term in an application's
function position must not be an abstraction (otherwise there is a β-redex). -/
inductive Normal : Term Var → Prop where
  | fvar (x : Var) : Normal (fvar x)
  | app {M N : Term Var} :
      Normal M → (∀ C, M ≠ Term.abs C) → Normal N → Normal (app M N)
  | abs (xs : Finset Var) {M : Term Var} :
      (∀ x ∉ xs, Normal (M ^ fvar x)) → Normal (Term.abs M)

/-- A **neutral** term is a normal term that is not an abstraction (a
variable-headed application spine). -/
def Neutral (M : Term Var) : Prop := Normal M ∧ ∀ C, M ≠ Term.abs C

theorem Neutral.fvar (x : Var) : Neutral (Term.fvar x : Term Var) :=
  ⟨Normal.fvar x, by rintro C ⟨⟩⟩

theorem Neutral.app {M N : Term Var} (hM : Neutral M) (hN : Normal N) :
    Neutral (Term.app M N) :=
  ⟨Normal.app hM.1 hM.2 hN, by rintro C ⟨⟩⟩

theorem Neutral.normal {M : Term Var} (h : Neutral M) : Normal M := h.1

/-
Normal terms are locally closed.
-/
@[grind]
theorem Normal.lc {M : Term Var} (h : Normal M) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ ih

theorem Neutral.lc {M : Term Var} (h : Neutral M) : LC M := h.1.lc

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
  revert h;
  intro hM;
  induction hM with
  | fvar z => rw [Term.subst_fvar]
              split <;> constructor
  | abs xs hM ih =>
    rename_i xs M
    apply Normal.abs ( xs ∪ { x } )
    intro z hz;
    convert ih z ( by aesop )
    rw  [Term.subst_open_var] <;> grind
  | app _ h₁ h₂ h₃ h₄ =>
    convert Normal.app h₃ _ h₄
    rw [Term.subst_app]
    intro C hC
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
    have g := FullBeta.redex_subst_cong_lc _ _ (fvar y) x g (by grind)
    unfold open' at g
    rw [<- subst_intro_openRec] at g
    exact g
    grind
    apply FullBeta.step_lc_r g
    grind
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

/-! ## Normal forms of η-expansion towers -/

/-
`(B)_1` of a neutral base `B` is normal.
-/
theorem Normal.etaExp_one {B : Term Var} (hne : Neutral B) :
    Normal (etaExp B 1) := by
  apply Normal.abs ∅;
  intro x hx; exact (by
  convert Normal.app hne.1 hne.2 ( Normal.fvar x ) using 1;
  exact open_app_bvar_lc ( Neutral.lc hne ) x);

/-
A tower of η-expansions over a **neutral** base has a normal (β-nf) form:
it β-collapses to `(B)_1` (or to `B` itself when `k = 0`).
-/
theorem etaExp_neutral_normalForm {B : Term Var} (hne : Neutral B) (k : ℕ) :
    ∃ M, (etaExp B k) ↠βᶠ M ∧ Normal M := by
  -- If k = 0, we can take M = B.
  by_cases hk : k = 0;
  · exact ⟨ B, by subst hk; exact Relation.ReflTransGen.refl, hne.1 ⟩;
  · obtain ⟨ k, rfl ⟩ := Nat.exists_eq_succ_of_ne_zero hk;
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
        apply Neutral.lc at hne
        rw [open_lc _ _ B hne, open_lc _ _ (B.etaExp (n+1)) (etaExp_lc hne _)]
        apply etaExp_app_collapse <;> grind
      · grind

/-! ## Structure of a single parallel η-step (Takahashi's Lemma 3.2) -/

/-- A tower `(Y)_k` reduces to `Z` in a single parallel η-step whenever `Y ⟹η Z`. -/
theorem parEta_etaExp {Y Z : Term Var} (h : ParEta Y Z) (k : ℕ) :
    ParEta (etaExp Y k) Z := by
  induction k with
  | zero => exact h
  | succ k ih => exact ParEta.eta (etaExp_lc (ParEta.regular h).1 k) ih

/-- Parallel β-reduction lifts through η-expansion towers. -/
theorem parBeta_etaExp_congr {A A' : Term Var} (h : Parallel A A') (k : ℕ) :
    Parallel (etaExp A k) (etaExp A' k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
      refine Parallel.abs (∅ : Finset Var) (fun x _ => ?_)
      rw [open_app_bvar_lc (etaExp_lc (by grind) k),
          open_app_bvar_lc (etaExp_lc (by grind) k)]
      exact Parallel.app ih (Parallel.fvar x)

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
  revert h;
  induction n : Term.size L using Nat.strong_induction_on generalizing L A B with
  | h n ih=>
  rintro ( h | h | h | h );
  · exact ⟨ 0, _, _, rfl, h, by assumption ⟩;
  · rename_i M hM;
    obtain ⟨ k, A', B', rfl, hA', hB' ⟩ := ih _ ( by
      simp +decide [ ← n, Term.size ];
      grind +splitImp ) rfl hM;
    exact ⟨ k + 1, A', B', rfl, hA', hB' ⟩

/-
**Lemma 3.2 (abstraction case).**
-/
theorem parEta_inv_abs {L A : Term Var}
    (h : ParEta L (Term.abs A)) :
    ∃ (k : ℕ) (A' : Term Var) (xs : Finset Var), L = etaExp (Term.abs A') k ∧
      ∀ x ∉ xs, ParEta (A' ^ fvar x) (A ^ fvar x) := by
  revert h;
  induction n : Term.size L using Nat.strong_induction_on generalizing L A with
  | h n ih =>
  rintro ( h | h | h | h );
  · exact ⟨ 0, _, h, rfl, by assumption ⟩;
  · rename_i M hM;
    obtain ⟨ k, A', xs, rfl, hA' ⟩ := ih _ ( by
      simp +decide [ ← n, Term.size ];
      linarith ) rfl hM;
    exact ⟨ k + 1, A', xs, rfl, hA' ⟩

/-! ## The reconstruction (core of Lemma 3.6) -/

/-- **Core reconstruction.**  If `A` is normal and `L ⟹η A` (a single parallel
η-step), then `L` β-reduces to a normal form; moreover if `A` is neutral, `L`
β-reduces to a tower `(B)_k` over a neutral base `B`. -/
theorem core_par {A : Term Var} (hA : Normal A) : ∀ L, ParEta L A →
    (∃ M, L ↠βᶠ M ∧ Normal M) ∧
    (Neutral A → ∃ k B, L ↠βᶠ (etaExp B k) ∧ Neutral B) := by
  induction hA with
  | fvar x =>
      intro L hL
      obtain ⟨k, rfl⟩ := parEta_inv_fvar hL
      exact ⟨etaExp_neutral_normalForm (Neutral.fvar x) k,
        fun _ => ⟨k, Term.fvar x, Relation.ReflTransGen.refl, Neutral.fvar x⟩⟩
  | @app M N hM hMne hN ihM ihN =>
      intro L hL
      obtain ⟨j, M', N', rfl, hM', hN'⟩ := parEta_inv_app hL
      have lcM' : LC M' := (ParEta.regular hM').1
      have lcN' : LC N' := (ParEta.regular hN').1
      obtain ⟨k1, B1, hB1red, hB1neu⟩ := (ihM M' hM').2 ⟨hM, hMne⟩
      obtain ⟨Nhat, hNred, hNnorm⟩ := (ihN N' hN').1
      have hcollapse : (app M' N') ↠βᶠ (app B1 Nhat) :=
        (FullBetaStar.appR lcN' hB1red).trans
          ((FullBetaStar.appL (etaExp_lc (Neutral.lc hB1neu) k1) hNred).trans
            (etaExp_app_collapse (Neutral.lc hB1neu) (Normal.lc hNnorm) k1))
      have hBneu : Neutral (app B1 Nhat) := Neutral.app hB1neu hNnorm
      have hcongr : (etaExp (app M' N') j) ↠βᶠ (etaExp (app B1 Nhat) j) :=
        etaExp_betaStar_congr (LC.app lcM' lcN') hcollapse j
      refine ⟨?_, fun _ => ⟨j, app B1 Nhat, hcongr, hBneu⟩⟩
      obtain ⟨M2, h2red, h2norm⟩ := etaExp_neutral_normalForm hBneu j
      exact ⟨M2, hcongr.trans h2red, h2norm⟩
  | @abs xs body hbody ihbody =>
      intro L hL
      obtain ⟨j, body', xs2, rfl, hred⟩ := parEta_inv_abs hL
      obtain ⟨x0, hx0⟩ :=
        Infinite.exists_notMem_finset (xs ∪ xs2 ∪ fv body ∪ fv body')
      simp only [Finset.mem_union, not_or] at hx0
      obtain ⟨⟨⟨hx0xs, hx0xs2⟩, _⟩, hx0b⟩ := hx0
      obtain ⟨C0, hC0red, hC0norm⟩ :=
        (ihbody x0 hx0xs (body' ^ fvar x0) (hred x0 hx0xs2)).1
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
        exact FullBetaStar.subst hC0red x0 (LC.fvar x)
      have hDnormal : Normal (Term.abs D) := by
        refine Normal.abs (∅ : Finset Var) (fun x _ => ?_)
        have e2 : (D : Term Var) ^ fvar x = Term.subst C0 x0 (fvar x) :=
          by  rw [hDdef]
              unfold open'
              rw [close_openRec_to_subst] <;> grind
        rw [e2]; exact Normal.subst_fvar hC0norm x0 x
      have hDabs : (Term.abs body') ↠βᶠ (Term.abs D) :=
        FullBetaStar.abs (∅ : Finset Var) (fun x _ => hDred x)
      have lcAbsBody' : LC (Term.abs body') :=
        LC.abs xs2 body' (fun x hx => (ParEta.regular (hred x hx)).1)
      refine ⟨⟨Term.abs D,
        (etaExp_betaStar_congr lcAbsBody' hDabs j).trans
          (etaExp_abs_collapse (Normal.lc hDnormal) j), hDnormal⟩, ?_⟩
      rintro ⟨-, hc⟩; exact absurd rfl (hc body)

/-
Substitutivity of parallel η-reduction.
-/
theorem ParEta.subst_par {A A' B B' : Term Var} (z : Var)
    (hA : ParEta A A') (hB : ParEta B B') :
    ParEta (Term.subst A z B) (Term.subst A' z B') := by
  induction hA generalizing B B';
  · unfold Term.subst;
    split_ifs <;> [ exact hB; exact ParEta.fvar _ ];
  · exact ParEta.app ( by aesop ) ( by aesop );
  · rename_i xs M M' hM h ih;
    exact ParEta.abs ( M ∪ { z } ) fun x hx => by
      grind +suggestions;
  · rename_i M M' hM hMM' ih; exact ParEta.eta ( Term.subst_lc hM hB.regular.1 ) ( ih hB ) ;

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
  revert hbody hZ;
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
      exact open_app_bvar_lc ( etaExp_lc hCabs j ) x
    · assumption

/-! ## Parallel η/β postponement (Takahashi's Lemma 3.4) -/

/-
**Lemma 3.4.**  A parallel η-step postpones over a parallel β-step:
`M ⟹η P ⟹β N` implies `M ⟹β P' ⟹η N` for some `P'`.
-/
theorem parEta_parBeta_postpone : Postpone (Parallel (Var := Var)) ParEta := by
  intros M N P hη hβ
  revert hη
  induction hβ generalizing M with
  | fvar x =>  grind +suggestions
  | app _ _ ih1 ih2 =>
    intro hM;
    obtain ⟨ k, M1, M2, rfl, hM1, hM2 ⟩ := parEta_inv_app hM
    obtain ⟨ P1, hP1, hP1' ⟩ := ih1 hM1
    obtain ⟨ P2, hP2, hP2' ⟩ := ih2 hM2
    use etaExp (app P1 P2) k;
    exact ⟨parBeta_etaExp_congr (Parallel.app hP1 hP2) k, parEta_etaExp (ParEta.app hP1' hP2') k⟩
  | abs xs _ _ =>
    rename_i xs M M' hβ ih;
    intro hM;
    obtain ⟨ k, M0, xs2, rfl, hM0 ⟩ := parEta_inv_abs hM;
    -- Pick `x0 ∉ xs ∪ xs2 ∪ fv M0 ∪ fv M'`.
    obtain ⟨x0, hx0⟩ : ∃ x0 : Var, x0 ∉ xs ∪ xs2 ∪ (fv M0 ∪ fv M') := by
      exact Set.Finite.exists_notMem ( Finset.finite_toSet _ );
    obtain ⟨ Q0, hQ0 ⟩ := ih x0 ( by aesop ) ( hM0 x0 ( by aesop ) );
    -- Set `M0' = closeRec 0 x0 Q0`.
    set M0' : Term Var := closeRec 0 x0 Q0;
    -- Prove the cofinite families for all `x` (using `LC Q0 = (ParBeta.regular ‹ParBeta (M0^x0) Q0›).2`, `subst_intro` with `x0∉fv M0`, `x0∉fv M'`, and `open_close_lc`):
    have h_cofinite : ∀ x ∉ xs ∪ xs2, Parallel (M0 ^ fvar x) (M0' ^ fvar x) ∧ ParEta (M0' ^ fvar x) (M' ^ fvar x) := by
      intro x hx
      have h_subst : M0 ^ fvar x = Term.subst (M0 ^ fvar x0) x0 (fvar x)  := by
        apply Term.subst_intro;
        grind
      have h_subst' : M0' ^ fvar x = Term.subst Q0 x0 (fvar x) := by
        unfold open'
        rw [close_openRec_to_subst] <;> grind
      have h_subst'' : M' ^ fvar x = Term.subst (M' ^ fvar x0) x0 (fvar x)  := by
        apply Term.subst_intro;
        grind;
      constructor
      · rw [ h_subst, h_subst' ]
        apply para_subst <;> grind
      · rw [h_subst', h_subst'']; exact ParEta.subst_par x0 hQ0.2 (ParEta.fvar x)
    refine ⟨ etaExp M0'.abs k, ?_, ?_ ⟩
    · apply parBeta_etaExp_congr;
      apply Parallel.abs
      exact fun x hx => h_cofinite x hx |>.1;
    · apply parEta_etaExp;
      apply ParEta.abs;
      exact fun x hx => h_cofinite x hx |>.2;
  | beta xs h₁ h₂ h₃ h₄ =>
    intro hη;
    rename_i xs M' N' M'' N''
    obtain ⟨ k, M₁, M₂, rfl, hM₁, hM₂ ⟩ := parEta_inv_app hη
    obtain ⟨ j, M₁b, xs', rfl, hM₁b ⟩ := parEta_inv_abs hM₁
    -- Pick `x0 ∉ xs ∪ xs' ∪ fv M₁b ∪ fv N'`.
    obtain ⟨x0, hx0'⟩ := Infinite.exists_notMem_finset (xs ∪ xs' ∪ fv M₁b ∪ fv N')
    have hx0 : x0 ∉ xs ∧ x0 ∉ xs' ∧ x0 ∉ fv M₁b ∧ x0 ∉ fv N' := by
      simp only [Finset.mem_union, not_or] at hx0'; tauto
    obtain ⟨ Q₁, hQ₁, hQ₂ ⟩ := h₃ x0 hx0.1 ( hM₁b x0 hx0.2.1 );
    -- Set `M₁b' = closeRec 0 x0 Q₁`.
    set M₁b' : Term Var := closeRec 0 x0 Q₁;
    -- Prove the cofinite families for all `x` (using `LC Q₁ = (ParBeta.regular ‹ParBeta (M₁b^x0) Q₁›).2`, `subst_intro` with `x0∉fv M₁b`, `x0∉fv N'`, and `open_close_lc`):
    have hM₁b'_family : ∀ x ∉ xs ∪ xs', Parallel (M₁b ^ fvar x) (M₁b' ^ fvar x) := by
      intro x hx;
      convert para_subst x0 hQ₁ ( Parallel.fvar x ) using 1;
      · rw [ Term.subst_intro ];
        exact hx0.2.2.1;
      · unfold open'
        rw [close_openRec_to_subst] <;> grind;
    have hM₁b'_family' : ∀ x ∉ xs ∪ xs', ParEta (M₁b' ^ fvar x) (N' ^ fvar x) := by
      intro x hx;
      convert ParEta.subst_par x0 hQ₂ ( ParEta.fvar x ) using 1;
      · unfold open'
        rw [close_openRec_to_subst] <;> grind;
      · rw [ Term.subst_intro x0 _ _ (by grind)]
        rw [subst_open] <;> grind
    obtain ⟨ P', hP', hP'' ⟩ := h₄ hM₂;
    refine ⟨ etaExp ( M₁b' ^ P' ) k, ?_, ?_ ⟩
    · convert parBeta_etaExp_congr ( parBeta_etaExp_abs_app ( xs ∪ xs' ) hM₁b'_family hP' j ) k
    · refine parEta_etaExp ?_ k
      apply ParEta.open_par
      exact hM₁b'_family'
      exact hP''


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
    (h : ParEta P Q) (hQ : Relation.Normalizable FullBeta Q) : Relation.Normalizable FullBeta P := by
  obtain ⟨N, hQN, hN⟩ := hQ
  -- `N` is the β-normal form of `Q`; it is locally closed and hence `Normal`.
  have hNlc : LC N := by  apply FullBeta.steps_lc_or_rfl at hQN
                          cases hQN with
                          | inl _ => grind
                          | inr hQN =>  subst Q
                                        apply ParEta.regular at h
                                        grind
  rw [<- parachain_iff_redex] at hQN
  -- Postpone the η-step past all β-steps: `P ⟹β* P' ⟹η N`.
  obtain ⟨P', hPP', hP'N⟩ := postpone_a parEta_parBeta_postpone h hQN
  -- The η-expansion `P' ⟹η N` of the normal form `N` has a β-normal form.
  apply betaNF_normal at hN
  obtain ⟨M, hP'M, hMnorm⟩ := (core_par hN P' hP'N).1
  rw [parachain_iff_redex] at hPP'
  apply  Normal.betaNF at hMnorm
  exact ⟨M, .trans hPP' hP'M, hMnorm⟩
  grind

theorem weakCommute_fullBeta_fullEta :
  Postpone (Relation.ReflTransGen (FullBeta (Var := Var))) (Relation.ReflTransGen FullEta) := by
    intros _ _ _ heta hbeta
    rw [<- parachain_iff_redex] at hbeta
    rw [<- paraEtachain_iff_redex] at heta
    have := postpone_ab parEta_parBeta_postpone heta hbeta
    grind [parachain_iff_redex, paraEtachain_iff_redex]

theorem eta_beta_postpone :
    Postpone (Relation.TransGen (FullBeta (Var := Var))) (Relation.ReflTransGen FullEta) := by
  intros _ _ _ heta hbeta
  exact star_over_plus weakCommute_fullBeta_fullEta strongLocal_fullBeta_fullEta heta hbeta

/-- **Takahashi's Lemma 3.7.**  If `P ⟹_η Q` (parallel η-reduction) and `P` is a
β-normal form, then `Q` is a β-normal form.

The proof uses strong η-postponement: a single parallel η-step is an η-reduction
`P ↠η Q`, so any β-step `Q ⟶β R` would give, by `eta_beta_postpone`, a non-empty
β-reduction `P ⟶β⁺ ⋯`, contradicting β-normality of `P`. -/
theorem parEta_betaNF {P Q : Term Var} (h : ParEta P Q) (hP : Relation.Normal FullBeta P) :
  Relation.Normal FullBeta Q := by
  intros hR
  obtain ⟨_, hR⟩ := hR
  obtain ⟨y, hy, _⟩ := eta_beta_postpone h.toFullEtaStar (.single hR)
  -- `hy : Relation.TransGen FullBeta P y` gives a first β-step out of `P`.
  obtain ⟨z, hz⟩ := exists_first_step hy
  apply hP
  exact ⟨z, hz⟩

/-- **A term has a βη-normal form ⇔ it has a β-normal form.** -/
theorem hasBetaEtaNF_iff_hasBetaNF (t : Term Var) :
  Relation.Normalizable FullBeta t ↔ Relation.Normalizable FullBetaEta t := by
  constructor
  · sorry
  · sorry
