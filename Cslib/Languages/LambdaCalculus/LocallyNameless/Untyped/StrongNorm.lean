/-
Copyright (c) 2025 David Wegmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wegmann
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.SnEtaStep
public import Cslib.Foundations.Relation.Confluence

/-! Strong normalization (termination) for full beta-reduction of untyped lambda calculus. -/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {t t' : Term Var}

open FullBeta Relation

attribute [grind =] Finset.union_singleton

/-- A single β-reduction step preserves strong normalization. -/
lemma sn_step (t_st_t' : t ⭢βᶠ t') (sn_t : SN FullBeta t) : SN FullBeta t' :=
  sn_t.of_rel t_st_t'

/-- Multiple β-reduction steps also preserve strong normalization. -/
lemma sn_steps (t_st_t' : t ↠βᶠ t') (sn_t : SN FullBeta t) : SN FullBeta t' :=
  sn_t.of_rel_reflTransGen t_st_t'

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Free variables are strongly normalizing. -/
lemma sn_fvar {x : Var} : SN FullBeta (fvar x) := by
  rw [SN_iff_SN_of_rel]
  grind only [cases Xi, cases Beta]

/-- An application is strongly normalizing if the left and right terms are strongly normalizing,
    as well as all possible future top level abstraction application beta reductions -/
lemma sn_app (t s : Term Var) (sn_t : SN FullBeta t) (sn_s : SN FullBeta s)
    (hβ : ∀ {t' s' : Term Var}, t ↠βᶠ t'.abs → s ↠βᶠ s' → SN FullBeta (t' ^ s')) :
    SN FullBeta (t.app s) := by
  induction sn_t generalizing s with
  | intro t ht ih_t =>
    induction sn_s with
    | intro s hs ih_s =>
      constructor
      intro u hstep
      cases hstep with
      | base h => cases h; grind
      | appL _ h_s_red => apply ih_s _ h_s_red
                          grind [Relation.ReflTransGen.head]
      | appR _ h_t_red => apply ih_t _ h_t_red _ (SN.intro hs)
                          grind [Relation.ReflTransGen.head]

/-- The left side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_left (M N : Term Var) (lc_N : Term.LC N) (sn_MN : SN FullBeta (M.app N)) :
    SN FullBeta M := by
  refine sn_MN.onFun_of_image (f := (·.app N)) |>.of_le fun _ _ => ?_
  exact Xi.appR lc_N

/-- The right side of a strongly normalizing application is strongly normalizing. -/
lemma sn_app_right (M N : Term Var) (lc_M : Term.LC M) (sn_MN : SN FullBeta (M.app N)) :
    SN FullBeta N := by
  refine sn_MN.onFun_of_image (f := M.app) |>.of_le fun _ _ => ?_
  exact Xi.appL lc_M

/-- A neutral term is a term of the form v t₁ … t_n where
    v is a variable and t₁ … t_n are strongly normalizing terms. -/
@[scoped grind]
inductive Neutral : Term Var → Prop
/-- Just a bound variable is neutral. -/
| bvar : ∀ n, Neutral (bvar n)
/-- Just a free variable is neutral. -/
| fvar : ∀ x, Neutral (fvar x)
/-- Applying a strongly normalizing term to a neutral term yields a neutral term. -/
| app : ∀ t1 t2, Neutral t1 → SN FullBeta t2 → Neutral (app t1 t2)

--attribute [scoped grind .] Neutral.bvar Neutral.fvar Neutral.app

/-- Neutral terms only reduce to other neutral terms in a single step -/
lemma neutral_step (Hneut : Neutral t) (Hstep : t ⭢βᶠ t') : Neutral t' := by
  induction Hneut generalizing t' with grind only [Neutral, cases Xi, sn_step]

/-- Neutral terms only reduce to other neutral terms in multiple steps -/
lemma neutral_steps (Hneut : Neutral t) (Hsteps : t ↠βᶠ t') : Neutral t' := by
  induction Hsteps <;> grind [neutral_step]

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Neutral terms are strongly normalizing. -/
lemma sn_neutral (Hneut : Neutral t) : SN FullBeta t := by
  induction Hneut with
  | app => grind only [→ neutral_steps, sn_app]
  | _ =>
    rw [SN_iff_SN_of_rel]
    grind only [cases Xi]

/-- A lambda abstraction is strongly normalizing if its body is strongly normalizing. -/
lemma sn_abs [DecidableEq Var] [HasFresh Var] {M N : Term Var} (sn_MN : SN FullBeta (M ^ N))
    (lc_N : LC N) : SN FullBeta (abs M) := by
  generalize h : (M ^ N) = M_open at sn_MN
  induction sn_MN generalizing M N with
  | intro =>
    constructor
    intro _ h_step
    cases h_step with
    | abs _ H => grind [step_open_cong_l _ _ _ _ H]
    | base _ => contradiction

/-- A term of the form λ M N P_1 … P_n is strongly normalizing if
      1. N is strongly normalizing,
      1. M ^ N P₁ … Pₙ is strongly normalizing,
      1. N is locally closed,
      1. M ^ N P₁ … Pₙ is locally closed -/
lemma sn_abs_app_multiApp [DecidableEq Var] [HasFresh Var] {Ps} {M N : Term Var}
    (sn_N : SN FullBeta N) (sn_MNPs : SN FullBeta (multiApp (M ^ N) Ps))
    (lc_N : LC N) (lc_MNPs : LC (multiApp (M ^ N) Ps)) :
    SN FullBeta (multiApp (M.abs.app N) Ps) := by
  induction Ps using List.reverseRecOn with
  | nil =>
    apply sn_app
    · grind [sn_abs]
    · exact sn_N
    · grind [→ steps_open_cong_abs, open_abs_lc, sn_steps]
  | append_singleton Ps P ih =>
    rw [multiApp_tail]
    apply sn_app
    · grind [cases LC, multiApp_tail, sn_app_left]
    · grind [multiApp_tail, sn_app_right]
    · intro Q' P' hstep1 hstep2
      have ⟨M', N', Ps', h_M_red, h_N_red, h_Ps_red, h_cases⟩ := invert_abs_multiApp_mst hstep1
      rcases h_cases with h_P | ⟨h_st1, h_st2⟩
      · induction Ps' using List.reverseRecOn with grind [multiApp_tail]
      · have innerSteps : (M ^ N).multiApp Ps ↠βᶠ (M' ^ N').multiApp Ps' := by
          trans
          · exact steps_multiApp_r h_Ps_red (by grind)
          · apply steps_multiApp_l
            · apply steps_open_cong_abs M M' N N' <;> grind [open_abs_lc]
            · grind [multiApp_steps_lc]
        refine sn_steps ?_ sn_MNPs
        rw [multiApp_tail]
        · calc ((M ^ N).multiApp Ps).app P
            _ ↠βᶠ ((M ^ N).multiApp Ps).app P' := by grind
            _ ↠βᶠ Q'.abs.app P' := redex_app_l_cong (.trans innerSteps h_st2) (by grind)
            _ ↠βᶠ Q' ^ P' := by
              rw [Relation.reflTransGen_iff_eq_or_transGen] at ⊢ innerSteps h_st2
              right
              refine Relation.TransGen.single (Xi.base (Beta.beta ?_ ?_))
              all_goals grind

lemma sn_eta_steps [DecidableEq Var] [HasFresh Var]
  (sn_t : SN (TransGen FullBeta) t) (t_st_t' : t ↠ηᶠ t') : SN FullBeta t' := by
  induction sn_t generalizing t' with
  | intro t h ih => constructor
                    intros t'' ht''
                    obtain ⟨_, g, _⟩ := eta_beta_postpone t_st_t' (.single ht'')
                    apply ih _ g
                    assumption


theorem acc_cong {α : Sort u} {r s : α → α → Prop}
    (hrel : ∀ a b, r a b ↔ s a b) (x : α) :
    Acc s x ↔ Acc r x := by
  constructor
  · intro h
    induction h with
    | intro y hy ih =>
      apply Acc.intro
      intro z hrz
      rw [hrel] at hrz
      exact ih z hrz
  · intro h
    induction h with
    | intro y hy ih =>
      apply Acc.intro
      intro z hsz
      rw [<- hrel] at hsz
      exact ih z hsz

lemma sn_eta_step [DecidableEq Var] [HasFresh Var]
  (sn_t : SN FullBeta t) (t_st_t' : t ↠ηᶠ t') : SN FullBeta t' :=
  sn_eta_steps (SN.transGen sn_t) t_st_t'

/-- **η-expansion preserves β-strong-normalisation (single step).**  If
`t ⟶η t'` (one η-step) and `t'` is β-strongly-normalising, then so is `t`. -/
theorem sn_eta_step_inv [DecidableEq Var] [HasFresh Var]
  {t t' : Term Var} (h : FullEta t t')
    (hs : Relation.SN (FullBeta : Term Var → Term Var → Prop) t') :
    Relation.SN (FullBeta : Term Var → Term Var → Prop) t :=
  sn_transfer hs (parEtaC_of_fullEta h)

theorem sn_eta_steps_inv [DecidableEq Var] [HasFresh Var]
    {t t' : Term Var} (h : t ↠ηᶠ t')
    (hs : Relation.SN (FullBeta : Term Var → Term Var → Prop) t') :
    Relation.SN (FullBeta : Term Var → Term Var → Prop) t := by
    induction h with grind [sn_eta_step_inv]

theorem sn_eta_steps_iff [DecidableEq Var] [HasFresh Var]
   (t_st_t' : t ↠ηᶠ t') : SN FullBeta t <-> SN FullBeta t' := by
   grind [sn_eta_step, sn_eta_steps_inv]

/-!
# βη strong normalisation equals β strong normalisation

This file proves the strong-normalisation form of η-postponement:

  **A term is βη-strongly-normalising iff it is β-strongly-normalising.**

In symbols, with `BetaEtaStep M N := FullBeta M N ∨ FullEta M N` the combined
one-step relation (from `Defs.lean`), and `SN R x := Acc (flip R) x`:

  `SN (Relation.TransGen BetaEtaStep) t ↔ SN (Relation.TransGen FullBeta) t`.

The forward direction is immediate (`FullBeta ⊆ BetaEtaStep`).  The backward
direction is de Vrijer's theorem (β-SN is preserved under η-expansion).  It is
proved here *not* via a term-size measure (which is known to fail for absorbed
β-steps), but via η-postponement: a β-step taken after a chain of η-steps can be
"reset" to a genuine β-reduction from the original term followed by η-steps,
using the strong single-step postponement lemma `eta_beta_postpone`.
-/


open Term Relation

/-! ## Generic accessibility conversions between a relation and its transitive closure -/

/-! ## η-reduction is well-founded -/

/-- `FullEta` (forward) is well-founded: every term is `flip FullEta`-accessible. -/
theorem wellFoundedFullEta [DecidableEq Var] [HasFresh Var] :
  Relation.Terminating (FullEta : Term Var → Term Var → Prop) :=
    Subrelation.wf (fun {a b} (h : flip FullEta a b) => FullEta.fullEta_size_lt h)
      (InvImage.wf size Nat.lt_wfRel.wf)

/-! ## The backward direction: β-SN implies βη-SN -/

/-- Inner step of the backward direction.  Given that every genuine β-reduct of
the *original* term `a0` is βη-accessible (`IHB`), and an η-chain `a0 ⟶η* a'`,
every η-accessible such `a'` is βη-accessible.

The proof is by induction on the η-accessibility of `a'`.  A β-step
`a' ⟶β b` is handled by η-postponement (`eta_beta_postpone`): from
`a0 ⟶η* a' ⟶β b` we obtain `a0 ⟶β⁺ d ⟶η* b`, so `d` is βη-accessible by `IHB`
and `b` follows by descent along η.  An η-step `a' ⟶η b` is handled by the inner
induction hypothesis. -/
theorem betaEtaSN_inner [DecidableEq Var] [HasFresh Var]
    (a0 : Term Var)
    (IHB : ∀ d, Relation.TransGen FullBeta a0 d → SN (FullBetaEta : Term Var → Term Var → Prop) d)
    {a' : Term Var} (hE : SN (FullEta : Term Var → Term Var → Prop) a') :
    a0 ↠ηᶠ a' → SN (FullBetaEta : Term Var → Term Var → Prop) a' := by
  induction hE with
  | intro a' hEacc IHE =>
      intro hrel
      refine Acc.intro a' ?_
      intro b hb
      -- hb : flip BetaEtaStep b a', i.e. BetaEtaStep a' b
      rcases hb with hbeta | heta
      · -- β-step a' ⟶β b
        obtain ⟨d, hd1, hd2⟩ := eta_beta_postpone hrel (.single hbeta)
        exact Relation.SN.of_rel_reflTransGen (IHB d hd1) (by grind)
      · -- η-step a' ⟶η b
        exact IHE b heta (hrel.tail heta)

/-- **Backward direction.** If `t` is β-strongly-normalising (accessible for
single β-steps), then it is βη-strongly-normalising. -/
theorem sn_betaEta_of_sn_fullBeta [DecidableEq Var] [HasFresh Var]
    {t : Term Var}
    (hB : SN ((Relation.TransGen FullBeta) : Term Var → Term Var → Prop) t) :
    SN (FullBetaEta : Term Var → Term Var → Prop) t := by
  induction hB with
  | intro t hBacc IHB =>
      -- IHB : ∀ d, TransGen FullBeta t d → Acc (flip BetaEtaStep) d
      exact betaEtaSN_inner t (fun d hd => IHB d hd) (wellFoundedFullEta.apply t)
        Relation.ReflTransGen.refl

/-! ## The forward direction and the equivalence -/

/-- **Forward direction.** βη-SN implies β-SN (β-steps are βη-steps). -/
theorem sn_fullBeta_of_sn_betaEta {t : Term Var}
    (h : SN (FullBetaEta : Term Var → Term Var → Prop) t) :
    SN (FullBeta : Term Var → Term Var → Prop) t := by
  refine Subrelation.accessible ?_ h
  intro a b hab
  exact Or.inl hab

/-- **A term is βη-strongly-normalising iff it is β-strongly-normalising.**

Here strong normalisation of a relation `R` at `t` is `Acc (flip R) t` (no
infinite `R`-reduction sequence starts at `t`), and `Relation.TransGen` is the
transitive closure (one-or-more steps). -/
theorem betaEta_sn_iff_beta_sn [DecidableEq Var] [HasFresh Var] (t : Term Var) :
    SN FullBetaEta t ↔ SN FullBeta t := by
  constructor
  · apply sn_fullBeta_of_sn_betaEta
  · intro h
    apply sn_betaEta_of_sn_fullBeta
    rw [Relation.SN.iff_transGen]
    assumption

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
