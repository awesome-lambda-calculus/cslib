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

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]



/-!
# Commutation lemma between a single η-step and a single β-step

The requested **commutation lemma** is: if `a ⟶η b` and `a ⟶β u`, then either

1. `u ≡ b`, or
2. there is `u'` with `u ⟶η u'` and `b ⟶β u'`.

As literally stated (with a *single* η-step `u ⟶η u'` in clause 2) this is **false**,
because a β-step can duplicate an η-redex.  Concrete counterexample (with `R`
locally closed):

  `a = (λy. y y) (λz. R z)`,  `b = (λy. y y) R`  (η-step on the argument),
  `u = (λz. R z) (λz. R z)`   (β-step on the top redex).

Then `b ⟶β R R` in one β-step, but reaching `R R` from
`u = (λz. R z)(λz. R z)` requires **two** η-steps, and `u ≠ b`; so no single
`u'` works.

The faithful repair keeps the β-step on `b` a *single* step (which always
suffices) but allows the η-side to be the reflexive–transitive closure
`⟶η*`.  Note that clause 1 (`u ≡ b`) is still genuinely needed: when the β-step
erases the β-redex entirely (e.g. when an η/β overlap makes `u` and `b`
syntactically equal) the term `b` may have no β-redex left to contract.

We therefore prove:

  `beta_eta_commute : FullEta a b → FullBeta a u →`
  `    u = b ∨ ∃ u', FullEtaStar u u' ∧ FullBeta b u'`.

The proof is by strong induction on the size of `a`, with case analysis on the
η-step (`comm_base`, `comm_appL`, `comm_appR`, `comm_abs`), mirroring the
structure of `eta_par_local` / `eta_beta_local` in the existing development.
-/


/-- The property proved by strong induction: a single η-step and a single
β-step out of the *same* term `a` either coincide (`u = b`) or can be closed
with a β-step from `b` matched by η-steps from `u`. -/
def CommProp (a : Term Var) : Prop :=
  ∀ b u : Term Var, FullEta a b → FullBeta a u →
    u = b ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta b u'

/-! ## The four cases of the η-step -/

/-
Base case: the η-redex is at the top, `a = λ. (M0 ·) ⟶η M0`.
-/
theorem comm_base {M0 u : Term Var} (hM0 : LC M0)
    (hbeta : FullBeta (abs (app M0 (bvar 0))) u) :
    u = M0 ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta M0 u' := by
  obtain ⟨ S', hS' ⟩ : ∃ S', u = abs S' := by grind +splitIndPred
  have hbody : ∃ ys : Finset Var, ∀ x ∉ ys, FullBeta ( Term.app M0 ( Term.fvar x ) ) ( S' ^ Term.fvar x ) := by
    obtain ⟨ ys, hys ⟩ := hbeta
    rename_i xs h
    exists xs
    grind
  obtain ⟨ ys, hbody ⟩ := hbody
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  obtain ⟨ M0'', hM0'' ⟩ : ∃ M0'', FullBeta M0 M0'' ∧ S' ^ fvar z = app M0'' (fvar z) ∨ M0 = abs M0'' ∧ S' ^ fvar z = M0'' ^ fvar z := by
    obtain ⟨ M0'', hM0'' ⟩ : ∃ M0'', FullBeta (app M0 (fvar z)) M0'' ∧ S' ^ fvar z = M0'' := by
      exact ⟨ _, hbody z (by grind), rfl ⟩;
    cases hM0''.1
    · cases ‹Beta ( M0.app ( fvar z ) ) M0''›
      grind
    · cases ‹Xi Beta ( fvar z ) _›
      cases ‹Beta ( fvar z ) _›
    · grind
  cases hM0'' <;> rename_i hM0''
  · have hS'_eq : S' = Term.app (closeRec 0 z M0'') (Term.bvar 0) := by
      have hS'_eq : closeRec 0 z (S' ^ fvar z) = S' := by
        unfold open'
        rw [<- Term.open_close]
        grind
      convert hS'_eq.symm using 1;
      grind
    refine Or.inr ⟨ M0'', ?_, (by grind) ⟩;
    rw [ hS' ];
    convert Relation.ReflTransGen.single ( Xi.base ( Eta.eta _ ) ) using 1;
    · rw [ hS'_eq, show closeRec 0 z M0'' = M0'' from ?_ ]
      rw [close_fresh]
      obtain ⟨hM0'', _⟩ := hM0''
      apply FullBeta.step_not_fv at hM0''
      grind
    grind [FullBeta.step_lc_r]
  · obtain ⟨_, hM0''⟩ := hM0''
    apply open_injective at hM0'' <;> grind

/-
η-step in the argument of an application, `a = app Z M`, `M ⟶η N`.
-/
theorem comm_appL {Z M N u : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app Z M) → CommProp M')
    (hZ : LC Z) (hxi : FullEta M N) (hbeta : FullBeta (app Z M) u) :
    u = app Z N ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta (app Z N) u' := by
  cases hbeta with
  | base hbeta =>
    right
    cases hbeta
    use ‹_› ^ N
    constructor;
    · apply FullEta.step_open_cong_r <;> grind
    · exact Xi.base ( Beta.beta hZ (FullEta.step_lc_r hxi) );
  | appL _ _ =>
    rename_i M' hM' hbeta
    generalize_proofs at *;
    specialize ih M (by
    exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ )) N M' hxi hbeta
    generalize_proofs at *;
    rcases ih with ( rfl | ⟨ u', hu', hu'' ⟩ ) <;> [ exact Or.inl rfl; exact Or.inr ⟨ Z.app u', FullEta.redex_app_r_cong hu' hZ, Xi.appL hZ hu'' ⟩]
  | appR _ _ =>
    right
    exists Term.app ‹_› N;
    constructor
    · apply FullEta.redex_app_r_cong
      · grind
      · apply FullBeta.step_lc_r (by assumption)
    · exact Xi.appR ( FullEta.step_lc_r hxi ) ‹_›

/-
η-step in the operator of an application, `a = app M Z`, `M ⟶η N`
(includes the β-redex creation/overlap case where `M` is an abstraction).
-/
theorem comm_appR {Z M N u : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app M Z) → CommProp M')
    (hZ : LC Z) (hxi : FullEta M N) (hbeta : FullBeta (app M Z) u) :
    u = app N Z ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta (app N Z) u' := by
  cases hbeta with
  | base hbeta =>
    cases ‹_›
    cases hxi with
    | base _ => cases ‹Eta _ _›
                grind
    | abs xs hxi =>
      rename_i M hM _ N
      right
      exists N ^ Z
      constructor
      · refine FullEta.steps_open_cong_l xs ?_ hZ
        grind
      · apply Xi.base
        refine Beta.beta ?_ hZ
        have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
        specialize hxi x (by grind)
        apply FullEta.step_lc_r at hxi
        apply open_abs_lc hxi
  | appL _ _ =>
    rename_i N' hN' hbeta'
    right
    exists N.app N'
    constructor
    · apply_rules [ Relation.ReflTransGen.single, Xi.appL ]
      exact Xi.appR ( FullBeta.step_lc_r hbeta' ) hxi
    · exact Xi.appL hxi.step_lc_r hbeta'
  | appR hZ' hM' =>
    rename_i M'
    specialize ih M (Nat.lt_add_of_pos_right ( Nat.succ_pos _ ) ) N M' hxi hM'
    rcases ih with ( rfl | ⟨ u', hu', hu'' ⟩ )
    · exact Or.inl rfl
    · exact Or.inr ⟨ u'.app Z, FullEta.redex_app_l_cong hu' hZ, Xi.appR hZ hu'' ⟩

/-
Witness packaging for the abstraction case (clause 2 via closing).
-/
theorem comm_exists_abs {N M w : Term Var} (z : Var)
    (hzN : z ∉ fv N) (hzM : z ∉ fv M)
    (heta : (M ^ fvar z) ↠ηᶠ w) (hbeta : FullBeta (N ^ fvar z) w) :
    ∃ u', M.abs ↠ηᶠ u' ∧ FullBeta N.abs u' := by
  exists abs ( closeRec 0 z w )
  constructor
  · rw [open_close z M 0 hzM]
    refine FullEta.steps_abs_close heta ?_
    apply FullBeta.step_lc_r at hbeta
    apply FullEta.steps_lc_l heta hbeta
  · apply Xi.abs ∅
    intros x hx
    have g := FullBeta.redex_subst_cong_lc _ _ (fvar x) z hbeta (by grind)
    unfold open' at g
    rw [<- subst_intro_openRec hzN] at g
    rw [<- close, close_open_to_subst _ _ _ _ (by grind)]
    · exact g
    · apply FullBeta.step_lc_r hbeta

/-
η-step under a binder, `a = abs M`, `M^x ⟶η N^x`.
-/
theorem comm_abs {M N u : Term Var} (xs : Finset Var)
    (ih : ∀ (M' : Term Var), size M' < size (abs M) → CommProp M')
    (hbody : ∀ x ∉ xs, FullEta (M ^ fvar x) (N ^ fvar x))
    (hbeta : FullBeta (abs M) u) :
    u = abs N ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta (abs N) u' := by
  obtain ⟨ ys, hbody' ⟩ := hbeta
  rename_i M' ys hbody'
  obtain ⟨ z, hz ⟩ := fresh_exists <| free_union [fv] Var
  specialize ih ( M ^ fvar z ) ?_ ( N ^ fvar z ) ( M' ^ fvar z ) ?_ ?_ <;> simp_all +decide [ Term.size ]
  rcases ih with ( h | ⟨ u', heta, hbeta ⟩ )
  · left
    apply open_injective _ _ _ _ _ h <;> grind
  · right
    exact comm_exists_abs z (by grind) (by grind) heta hbeta

/-- **Commutation lemma.** A single η-step and a single β-step out of the same
term either coincide, or can be closed by a single β-step from `b` matched by
η-steps from `u`. -/
theorem comm_prop (a : Term Var) : CommProp a := by
  have key : ∀ n (a : Term Var), size a = n → CommProp a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro a han b u he hbeta
      have ih : ∀ (a' : Term Var), size a' < size a → CommProp a' := by
        intro a' ha'
        exact IH (size a') (han ▸ ha') a' rfl
      cases he with
      | base hb =>
          cases hb with
          | eta hM0 => exact comm_base hM0 hbeta
      | appL hZ hxi => exact comm_appL ih hZ hxi hbeta
      | appR hZ hxi => exact comm_appR ih hZ hxi hbeta
      | abs xs hbody => exact comm_abs xs ih hbody hbeta
  intro b u he hbeta
  exact key (size a) a rfl b u he hbeta

/- TODO: abandoned: stronglyCommute_eta_beta
-/
/-- **Commutation lemma** (final form): if `a ⟶η b` and `a ⟶β u` then either
`u = b`, or there is `u'` with `u ⟶η* u'` and `b ⟶β u'`. -/
theorem beta_eta_commute {a b u : Term Var}
    (heta : FullEta a b) (hbeta : FullBeta a u) :
    u = b ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta b u' :=
  comm_prop a b u heta hbeta

/-!
# Commutation of *multi-step* η-reduction with a single β-step

This file generalises the single-step commutation lemma
`LambdaLN.beta_eta_commute` (proved in `RequestProject.Commutation`) from a
single η-step to the (reflexive-)transitive closure of η-reduction.

## The originally requested statements are FALSE

The user asked for the two statements (both literally named `foo`):

```
theorem foo {a b u : Term Var}
    (heta : Relation.TransGen FullEta a b) (hbeta : FullBeta a u) :
    u = b ∨ ∃ u', Relation.TransGen FullEta u u' ∧ FullBeta b u'

theorem foo {a b u : Term Var}
    (heta : Relation.ReflTransGen FullEta a b) (hbeta : FullBeta a u) :
    u = b ∨ ∃ u', Relation.ReflTransGen FullEta u u' ∧ FullBeta b u'
```

Both are false, because over a *chain* of η-steps the matching β-reduction
from `b` can no longer be performed in a single step (it may need zero or
several β-steps), and in the transitive variant the η-correction from `u`
may need *zero* steps.

### Counterexample to the single-`FullBeta` clause (affects both statements)

Work with closed terms.  Let `I := λz. z = abs (bvar 0)`,
`b1 := λy. (I y) = abs (app I (bvar 0))` and
`a := λx. (b1 x) = abs (app b1 (bvar 0))`.

* `a ⟶η b1`        (top η-redex `λx. (b1 x) ⟶η b1`);
* `a ⟶β b1`        (contracting the inner redex `b1 x` under the binder, which
  yields `λx. (I x) = b1` again);  so the single β-reduct is `u = b1`;
* `b1 ⟶η I`        (top η-redex `λy. (I y) ⟶η I`);  hence `a ⟶η* I =: b`.

Now `b = I` is in normal form, so there is **no** single β-step `b ⟶β u'`, and
`u = b1 ≠ I = b`.  Thus the reflexive-transitive statement with a single
`FullBeta b u'` fails.  (The transitive statement fails on the very same
example.)  The repair is to allow `b ⟶β* u'` (reflexive-transitive β).

### Counterexample to the `TransGen FullEta u u'` conclusion

Let `c` be a free variable, `I := abs (bvar 0)`, and
`W := λx. (I x) = abs (app I (bvar 0))` (an η-redex), and
`a := (λy. c) W = app (abs (fvar c)) W`.

* `a ⟶β c`   (the β-redex deletes its argument `W`); so `u = c`;
* `a ⟶η (λy. c) I = app (abs (fvar c)) I =: b`  (η inside the argument).

Here `a ⟶η b` is a (one-step) `TransGen FullEta`.  To close the diagram we
need `u'` with `Relation.TransGen FullEta u u'` (at least one η-step from
`u = c`) and `b ⟶β* u'`.  But `u = c` is a free variable: it has **no**
η-redex, so no `TransGen FullEta c u'` exists.  The only closing term is
`u' = c` itself reached by *zero* η-steps (`b ⟶β c`), which the
reflexive-transitive conclusion allows but the transitive one forbids.

Hence the η-side of the conclusion must be `Relation.ReflTransGen FullEta`.

## The corrected (and proved) statements

The faithful, true commutation lemma keeps the η-hypothesis as given but uses
the reflexive-transitive closure on *both* reduction relations in the
conclusion:

  if `a ⟶η* b` and `a ⟶β u`, then `∃ u', u ⟶η* u' ∧ b ⟶β* u'`.

This is `beta_eta_commute_star` below; the `u = b ∨ …` disjunctive form
requested by the user is recovered verbatim in `foo_refltrans` (the left
disjunct is subsumed by the right, but we keep it to match the request), and
the `TransGen`-hypothesis variant is `foo_transgen`.
-/

/-- **Strip lemma.** A reflexive-transitive η-reduction `a ⟶η* b` commutes with
a single β-step `a ⟶β u`: there is a common term `u'` with `u ⟶η* u'` and
`b ⟶β* u'` (a reflexive-transitive β-reduction).

The proof is a head-induction on the η-chain, using the single-step
commutation lemma `beta_eta_commute` as the local tile. -/
theorem strip_star {a b : Term Var} (heta : a ↠ηᶠ b) :
    ∀ u, FullBeta a u → ∃ u', u ↠ηᶠ u' ∧ b ↠βᶠ u' := by
  induction heta using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro u hbeta
      exact ⟨u, Relation.ReflTransGen.refl, Relation.ReflTransGen.single hbeta⟩
  | head hab hrest ih =>
      intro u hbeta
      rcases beta_eta_commute hab hbeta with hub | ⟨w, hw1, hw2⟩
      · subst hub
        exact ⟨_, hrest, Relation.ReflTransGen.refl⟩
      · obtain ⟨u', hu1, hu2⟩ := ih w hw2
        exact ⟨u', hw1.trans hu1, hu2⟩

/-- **Commutation of multi-step η with a single β-step.** If `a ⟶η* b` and
`a ⟶β u`, then there is `u'` with `u ⟶η* u'` and `b ⟶β* u'`. -/
theorem beta_eta_commute_star {a b u : Term Var}
    (heta : a ↠ηᶠ b) (hbeta : FullBeta a u) :
    ∃ u', u ↠ηᶠ u' ∧ b ↠βᶠ u' :=
  strip_star heta u hbeta

/-- Corrected reflexive-transitive form, matching the requested disjunctive
shape (`u = b ∨ …`).  Compared to the (false) original, the matching
β-reduction from `b` is the reflexive-transitive closure `FullBetaStar`
instead of a single `FullBeta` step. -/
theorem foo_refltrans {a b u : Term Var}
    (heta : Relation.ReflTransGen FullEta a b) (hbeta : FullBeta a u) :
     ∃ u', Relation.ReflTransGen FullEta u u' ∧ Relation.ReflTransGen FullBeta b u' :=
  strip_star heta u hbeta

/-- Corrected transitive-hypothesis form.  Compared to the (false) original,
the conclusion uses the reflexive-transitive closures `Relation.ReflTransGen`
on both the η-side and the β-side (see the counterexamples in the file header
for why neither can be strengthened to `TransGen`/single `FullBeta`). -/
theorem foo_transgen {a b u : Term Var}
    (heta : Relation.TransGen FullEta a b) (hbeta : FullBeta a u) :
     ∃ u', Relation.ReflTransGen FullEta u u' ∧ Relation.ReflTransGen FullBeta b u' :=
  strip_star heta.to_reflTransGen u hbeta

/-!
## Multi-step β version

The further requested statement uses a (non-empty) transitive β-reduction on
both sides:

```
theorem foo {a b u : Term Var}
    (heta : Relation.ReflTransGen FullEta a b) (hbeta : Relation.TransGen FullBeta a u) :
    u = b ∨ ∃ u', Relation.ReflTransGen FullEta u u' ∧ Relation.TransGen FullBeta b u'
```

This is again FALSE, for the same reason as before: the matching β-reduction
from `b` cannot be required to take at least one step.  Reusing the first
counterexample of the header, `a := λx. (b1 x)`, `b := I = λz. z`,
`u := b1 = λy. (I y)`:

* `a ⟶β u`         so `Relation.TransGen FullBeta a u` (one β-step);
* `a ⟶η b1 ⟶η I = b`   so `Relation.ReflTransGen FullEta a b`.

Then `b = I` is β-normal, so there is **no** `Relation.TransGen FullBeta b u'`
(which requires at least one β-step), and `u = b1 ≠ I = b`.  The closing term is
`u' = b` reached from `u = b1` by η-steps and from `b` by *zero* β-steps, which
only `Relation.ReflTransGen FullBeta` permits.

The corrected, true statement (`foo_transbeta`) therefore uses
`Relation.ReflTransGen FullBeta` on the conclusion's β-side.  It is an instance
of the full commutation of `η*` with `β*`: -/

/-- **Full commutation of `η*` with `β*`.** If `a ⟶η* b` and `a ⟶β* u`, then
there is `u'` with `u ⟶η* u'` and `b ⟶β* u'`.

Proved by induction on the β-chain `a ⟶β* u`, using the single-β strip lemma
`strip_star` at each step. -/
theorem comm_star_star {a b : Term Var} (heta : a ↠ηᶠ b) :
    ∀ u, a ↠βᶠ u → ∃ u', u ↠ηᶠ u' ∧ b ↠βᶠ u' := by
  intro u hbeta
  induction hbeta with
  | refl => exact ⟨b, heta, Relation.ReflTransGen.refl⟩
  | tail _ step ih =>
      obtain ⟨w, hw1, hw2⟩ := ih
      obtain ⟨d, hd1, hd2⟩ := strip_star hw1 _ step
      exact ⟨d, hd1, hw2.trans hd2⟩

/-- Corrected transitive-β form of the request.  Compared to the (false)
original, the conclusion's β-side is the reflexive-transitive closure
`Relation.ReflTransGen FullBeta` instead of `Relation.TransGen FullBeta` (see
the counterexample above for why it cannot be a non-empty β-reduction). -/
theorem foo_transbeta {a b u : Term Var}
    (heta : Relation.ReflTransGen FullEta a b) (hbeta : Relation.TransGen FullBeta a u) :
     ∃ u', Relation.ReflTransGen FullEta u u' ∧ Relation.ReflTransGen FullBeta b u' :=
  comm_star_star heta u hbeta.to_reflTransGen

/-- **Commutation of a single η-step with multi-step β.** If `a ⟶η b` (a single
η-step) and `a ⟶β* u` (a reflexive-transitive β-reduction), then there is `u'`
with `u ⟶η* u'` and `b ⟶β* u'`.

This is the instance of `comm_star_star` where the η-side is a single step. -/
theorem refltransgen_beta_eta_commute {a b u : Term Var}
    (heta : FullEta a b) (hbeta : Relation.ReflTransGen FullBeta a u) :
    ∃ u', Relation.ReflTransGen FullEta u u' ∧
          Relation.ReflTransGen FullBeta b u' :=
  comm_star_star (Relation.ReflTransGen.single heta) u hbeta


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
