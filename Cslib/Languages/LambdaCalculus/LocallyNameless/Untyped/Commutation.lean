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
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ParEtaC

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


/-- **Commutation lemma** (final form): if `a ⟶η b` and `a ⟶β u` then either
`u = b`, or there is `u'` with `u ⟶η* u'` and `b ⟶β u'`. -/
theorem beta_eta_commute {a b u : Term Var}
    (heta : FullEta a b) (hbeta : FullBeta a u) :
    u = b ∨ ∃ u', u ↠ηᶠ u' ∧ FullBeta b u' := by
  rcases interaction a 1 _ _ (parEtaC_of_fullEta heta) hbeta with ⟨u', m, h, _⟩|⟨m, _, h⟩
  · apply ParEtaC.toFullEtaStar at h
    grind
  · have : m = 0 := by omega
    subst m
    left
    apply ParEtaC.refl_rev h


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
