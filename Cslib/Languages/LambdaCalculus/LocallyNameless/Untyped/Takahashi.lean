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

variable {Var : Type u} [Infinite Var] [DecidableEq Var] [HasFresh Var]

/-- The statement proved by induction: η postpones over a single parallel β-step
out of `M`. -/
public def TakaProp (M : Term Var) : Prop :=
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
theorem eta_postponement {M N : Term Var} (h : M ↠βηᶠ N) :
    ∃ L, M ↠βᶠ L ∧ L ↠ηᶠ N := by
  obtain ⟨L, hL₁, hL₂⟩ := postpone localPostpone_parBeta_fullEta (Relation.ReflTransGen.mono (fun a b hab => by
    cases hab <;> [exact Or.inl (step_to_para ‹_›); exact Or.inr ‹_›]) h)
  rw [parachain_iff_redex] at hL₁
  exact ⟨ L, hL₁, hL₂ ⟩

variable {α : Type*}

/-- Weak commutation: a `B`-star followed by an `A`-star can be reorganized into
an `A`-star followed by a `B`-star. -/
def WeakCommute (A B : α → α → Prop) : Prop :=
  ∀ ⦃p q r⦄, Relation.ReflTransGen B p q → Relation.ReflTransGen A q r → ∃ s, Relation.ReflTransGen A p s ∧ Relation.ReflTransGen B s r

/-- Strong local postponement: a single `B`-step followed by a single `A`-step
reorganizes into a *non-empty* sequence of `A`-steps followed by a `B`-star. -/
def StrongLocal (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → A y z → ∃ w, Relation.TransGen A x w ∧ Relation.ReflTransGen B w z

/-
A single `B`-step followed by a non-empty `A`-sequence reorganizes into a
non-empty `A`-sequence followed by a `B`-star.
-/
theorem single_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {x y z : α} (hxy : B x y) (hyz : Relation.TransGen A y z) :
    ∃ (w : α), Relation.TransGen A x w ∧ Relation.ReflTransGen B w z := by
  induction hyz with
  | single hyz => exact hL hxy hyz
  | tail h₁ h₂ h₃ =>
    obtain ⟨ w, hw₁, hw₂ ⟩ := h₃;
    exact Exists.elim (hW hw₂ (Relation.ReflTransGen.single h₂)) fun s hs => ⟨s, hw₁.trans_left hs.1, hs.2⟩

/-
A `B`-star followed by a non-empty `A`-sequence reorganizes into a non-empty
`A`-sequence followed by a `B`-star.
-/
theorem star_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {a b c : α} (hab : Relation.ReflTransGen B a b) (hbc : Relation.TransGen A b c) :
    ∃ w, Relation.TransGen A a w ∧ Relation.ReflTransGen B w c := by
  induction hab generalizing c with
  | refl => exact ⟨ c, hbc, by rfl ⟩
  | tail _ hB hA =>
    exact single_over_plus hW hL hB hbc |> fun ⟨ w, hw₁, hw₂ ⟩ => hA hw₁ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂.trans hw₂ ⟩


/-! ## Congruence lemmas for non-empty β-reduction -/

/-
Left-application congruence for non-empty full β-reduction.
-/
omit [Infinite Var] in
theorem fullBetaTrans_appL {Z M N : Term Var} (hZ : LC Z)
    (h : Relation.TransGen FullBeta M N) :
    Relation.TransGen FullBeta (app Z M) (app Z N) := by
  induction h;
  · exact .single ( Xi.appL hZ ‹_› );
  · rename_i h₁ h₂ h₃;
    exact h₃.tail ( Xi.appL hZ h₂ )

/-
Right-application congruence for non-empty full β-reduction.
-/
omit [Infinite Var] in
theorem fullBetaTrans_appR {Z M N : Term Var} (hZ : LC Z)
    (h : Relation.TransGen FullBeta M N) :
    Relation.TransGen FullBeta (app M Z) (app N Z) := by
  unfold FullBeta;
  induction h;
  · exact .single ( Xi.appR hZ ‹_› );
  · rename_i h₁ h₂ h₃;
    exact h₃.tail ( Xi.appR hZ h₂ )

/-
Abstraction (via closing) congruence for non-empty full β-reduction.
-/
theorem fullBetaTrans_abs_close (x : Var) {A B : Term Var}
    (h : Relation.TransGen FullBeta A B) :
    Relation.TransGen FullBeta (abs (closeRec 0 x A)) (abs (closeRec 0 x B)) := by
  revert h;
  intro h
  induction h with
  | single h => exact .single (FullBeta.step_abs_close h);
  | tail h₁ h₂ h₃ => apply h₃.tail (FullBeta.step_abs_close h₂)

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
  refine' ⟨ _, _, _ ⟩
  exact abs ( app P ( bvar 0 ) )
  · refine' Relation.TransGen.single _
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
  rcases hbeta with ( _ | _ | _ | _ );
  · rcases ‹_› with ( _ | _ | _ | _ );
    rcases ‹Beta _ _› with ( _ | _ | _ | _ );
    rename_i k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆;
    refine ⟨ _, Relation.TransGen.single (Xi.base (Beta.beta hZ (FullEta.step_lc_l he) ) ), ?_ ⟩
    apply FullEta.step_open_cong_r hZ (FullEta.step_lc_l he) he
  · obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 ( by
      exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ) N0 _ he ‹_›;
    exact ⟨ _, fullBetaTrans_appL hZ hQ₁, (FullEta.redex_app_r_cong hQ₂ (by assumption))⟩;
  · rename_i N hN hN';
    exact ⟨ _, fullBetaTrans_appR (FullEta.step_lc_l he) (.single hN), FullEta.redex_app_r_cong (.single he) (FullBeta.step_lc_r hN)⟩;

/-
The β-redex-creation subcase where the operator η-reduces (by a top η-redex)
to an abstraction.
-/
theorem takaP_appR_redex {W Z : Term Var} (hZ : LC Z) (hW : LC (abs W)) :
    ∃ Q, Relation.TransGen FullBeta
        (app (abs (app (abs W) (bvar 0))) Z) Q ∧ Q ↠ηᶠ (W ^ Z) := by
  -- Prove that `LC (abs (app (abs W) (bvar 0)))` by showing it is locally closed.
  have hLC : LC (Term.abs (Term.app (Term.abs W) (Term.bvar 0))) := by
    apply Term.LC.abs ∅
    grind
  exists W ^ Z
  constructor
  · apply Relation.TransGen.tail
    · apply Relation.TransGen.single
      apply Xi.base
      constructor <;> grind
    · apply Xi.base
      unfold open'
      conv =>
        left
        unfold openRec
      rw [open_lc _ _ W.abs hW]
      constructor <;> grind
  · grind

/-
The β-redex-creation subcase where the operator is an abstraction whose body
η-reduces.
-/
theorem takaP_appR_create {M0b W Z : Term Var} (xs : Finset Var) (hZ : LC Z)
    (hM0 : LC (abs M0b))
    (hbody : ∀ x ∉ xs, FullEta (M0b ^ fvar x) (W ^ fvar x)) :
    ∃ Q, Relation.TransGen FullBeta (app (abs M0b) Z) Q ∧ Q ↠ηᶠ (W ^ Z) := by
  use M0b ^ Z;
  constructor;
  · exact .single ( Xi.base ( Beta.beta hM0 hZ ) );
  · convert open_body xs ( fun x hx => Relation.ReflTransGen.single ( hbody x hx ) ) hZ using 1

/-
η-step in the operator of an application (includes β-redex creation).
-/
theorem takaP_appR {M0 Z N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app M0 Z) → TakaPlusProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hbeta : FullBeta (app N0 Z) P) :
    ∃ Q, Relation.TransGen FullBeta (app M0 Z) Q ∧ Q ↠ηᶠ P := by
  cases hbeta with
  | appL _ _ =>
    rename_i N hN hN';
    refine ⟨ _, fullBetaTrans_appL ?_ ( Relation.TransGen.single hN' ), ?_ ⟩;
    · apply FullEta.step_lc_l
      assumption
    · grind +suggestions;
  | appR _ _ =>
    rename_i N hN hZ';
    obtain ⟨w, hw1, hw2⟩ : ∃ w, Relation.TransGen FullBeta M0 w ∧ w ↠ηᶠ N := by
      exact ih M0 ( by simp +decide [ Term.size ] ) N0 N he ( by tauto );
    refine ⟨ _, fullBetaTrans_appR hZ' hw1, FullEta.redex_app_l_cong hw2 hZ'⟩
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
/-
Witness packaging for the abstraction case (β side via closing).
-/
theorem exists_Q_abs_plus {M0 P0 W : Term Var} (z : Var)
    (hz0 : z ∉ fv M0) (hzP : z ∉ fv P0)
    (hbeta : Relation.TransGen FullBeta (M0 ^ fvar z) W)
    (heta : W ↠ηᶠ (P0 ^ fvar z)) :
    ∃ Q, Relation.TransGen FullBeta (Term.abs M0) Q ∧ Q ↠ηᶠ (Term.abs P0) := by
  -- By `fullBetaTrans_abs_close z hbeta`, we get `Relation.TransGen FullBeta (abs (closeRec 0 z (M0 ^ fvar z))) (abs (closeRec 0 z W))`.
  have h_trans : Relation.TransGen FullBeta (abs (closeRec 0 z (M0 ^ fvar z))) (abs (closeRec 0 z W)) := by
    convert fullBetaTrans_abs_close z hbeta using 1;
  refine' ⟨ _, _, _ ⟩;
  exact ( closeRec 0 z W ).abs;
  · convert h_trans using 1;
    rw [ show closeRec 0 z ( M0 ^ fvar z ) = M0 from ?_ ];
    symm
    apply Term.open_close _ _ _ hz0
  · rw [<- close_open z W] at heta
    apply FullEta.redex_abs_cong
    · sorry
    · sorry
    · sorry
    · sorry
    -- convert XiStar.abs_close ( fun _ _ => Eta.regular ) ( fun _ _ hab y w hw => Eta.subst hab y hw ) z heta using 1;
    -- exact congr_arg _ ( by exact Eq.symm ( Term.close_open hzP 0 ) )
-/

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
    have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
    specialize ih (M0 ^ fvar z) (by simp +decide [Term.size]) (N0 ^ fvar z) (‹_› ^ fvar z) (hbody z (by grind)) (by grind)
    obtain ⟨Q, hqbeta, hqeta⟩ := ih
    have qlc : Q.LC := by refine Xi.steps_lc_r ?_  hqbeta
                          intros _ _ _
                          apply FullBeta.step_lc_r
                          assumption
    exists (Q.close z).abs
    rw [<- close_open z Q qlc] at hqbeta hqeta
    rename_i N
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
  intro p q r hpq hqr;
  obtain ⟨ s, hs ⟩ := postpone ( localPostpone_parBeta_fullEta ) ( by
    convert hpq.mono _ |> Relation.ReflTransGen.trans <| hqr.mono _ using 1;
    · exact fun a b hab => Or.inr hab;
    · exact fun a b hab => Or.inl <| step_to_para hab);
  obtain ⟨hs1, hs2⟩ := hs
  rw [parachain_iff_redex] at hs1
  exact ⟨s, hs1, hs2⟩

/-! ## Main theorem -/

/-- **Strong η-postponement (single β-step).**  If `t ⟶η* t'` and `t' ⟶β t''`,
then there is `y` with a non-empty β-reduction `t ⟶β⁺ y` and `y ⟶η* t''`. -/
theorem eta_beta_postpone {t t' t'' : Term Var}
    (htt' : t ↠ηᶠ t') (ht'' : FullBeta t' t'') :
    ∃ y, Relation.TransGen FullBeta t y ∧ y ↠ηᶠ t'' :=
  star_over_plus weakCommute_fullBeta_fullEta
    strongLocal_fullBeta_fullEta htt' (Relation.TransGen.single ht'')

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
