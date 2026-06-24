import RequestProject.EtaPostponement

/-!
# Strong η-postponement (single-β version)

This file proves the "local" / single-step version of η-postponement requested:
if `t ⟶η* t'` (reflexive-transitive η) and `t' ⟶β t''` (a single full β-step),
then there is `y` with `t ⟶β⁺ y` (a *non-empty* sequence of β-steps) and
`y ⟶η* t''`.

In symbols:

  `FullEtaStar t t' → FullBeta t' t'' → ∃ y, Relation.TransGen FullBeta t y ∧ FullEtaStar y t''`.

The crux is the strong local commutation `eta_beta_local`:
`FullEta M N → FullBeta N P → ∃ Q, FullBeta⁺ M Q ∧ FullEta* Q P`,
proved by strong induction on term size, mirroring the parallel-β version
`eta_par_local` but tracking a genuine (non-empty) β-reduction.
-/

open scoped Classical

universe u

/-! ## Abstract relational scaffolding -/

namespace AbstractPostpone

open Relation

variable {α : Type*} {A B : α → α → Prop}

/-- Weak commutation: a `B`-star followed by an `A`-star can be reorganized into
an `A`-star followed by a `B`-star. -/
def WeakCommute (A B : α → α → Prop) : Prop :=
  ∀ ⦃p q r⦄, ReflTransGen B p q → ReflTransGen A q r → ∃ s, ReflTransGen A p s ∧ ReflTransGen B s r

/-- Strong local postponement: a single `B`-step followed by a single `A`-step
reorganizes into a *non-empty* sequence of `A`-steps followed by a `B`-star. -/
def StrongLocal (A B : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, B x y → A y z → ∃ w, TransGen A x w ∧ ReflTransGen B w z

/-
A single `B`-step followed by a non-empty `A`-sequence reorganizes into a
non-empty `A`-sequence followed by a `B`-star.
-/
theorem single_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {x y z : α} (hxy : B x y) (hyz : TransGen A y z) :
    ∃ w, TransGen A x w ∧ ReflTransGen B w z := by
  induction' hyz with y z hyz ih;
  · exact hL hxy z;
  · rename_i h₁ h₂ h₃;
    obtain ⟨ w, hw₁, hw₂ ⟩ := h₃;
    exact Exists.elim ( hW hw₂ ( Relation.ReflTransGen.single h₂ ) ) fun s hs => ⟨ s, hw₁.trans_left hs.1, hs.2 ⟩

/-
A `B`-star followed by a non-empty `A`-sequence reorganizes into a non-empty
`A`-sequence followed by a `B`-star.
-/
theorem star_over_plus (hW : WeakCommute A B) (hL : StrongLocal A B)
    {a b c : α} (hab : ReflTransGen B a b) (hbc : TransGen A b c) :
    ∃ w, TransGen A a w ∧ ReflTransGen B w c := by
  induction' hab with d hd ih generalizing c;
  · exact ⟨ c, hbc, by rfl ⟩;
  · rename_i hB hA;
    exact single_over_plus hW hL hB hbc |> fun ⟨ w, hw₁, hw₂ ⟩ => hA hw₁ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂.trans hw₂ ⟩

end AbstractPostpone

namespace LambdaLN

open Term

variable {Var : Type u} [Infinite Var]

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
  induction' h with B hB h ih;
  · exact .single ( Xi.abs_close ( fun _ _ => Beta.regular ) ( fun _ _ hab y w hw => Beta.subst hab y hw ) x hB );
  · rename_i h₁ h₂ h₃;
    refine' h₃.tail _;
    apply Xi.abs_close (fun _ _ => Beta.regular) (fun _ _ hab y w hw => Beta.subst hab y hw) x h₂

/-! ## The strong local commutation property -/

/-- The property proved by strong induction: a single η-step followed by a single
β-step out of `M` reorganizes into a non-empty β-sequence followed by η-steps. -/
def TakaPlusProp (M : Term Var) : Prop :=
  ∀ N P : Term Var, FullEta M N → FullBeta N P →
    ∃ Q, Relation.TransGen FullBeta M Q ∧ FullEtaStar Q P

/-
Base case: the η-redex is at the top.
-/
theorem takaP_base {M0 P : Term Var} (hM0 : LC M0) (hbeta : FullBeta M0 P) :
    ∃ Q, Relation.TransGen FullBeta (abs (app M0 (bvar 0))) Q ∧ FullEtaStar Q P := by
  refine' ⟨ _, _, _ ⟩;
  exact abs ( app P ( bvar 0 ) );
  · refine' Relation.TransGen.single _;
    apply Xi.abs ∅;
    simp +decide [ Term.openRec, Term.openRec_lc hM0, Term.openRec_lc ( FullBeta.lc_right hbeta ) ];
    exact fun x => Xi.appR ( LC.fvar x ) hbeta;
  · exact .single ( Xi.base ( Eta.eta ( FullBeta.lc_right hbeta ) ) )

/-
η-step in the argument of an application.
-/
theorem takaP_appL {Z M0 N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app Z M0) → TakaPlusProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hbeta : FullBeta (app Z N0) P) :
    ∃ Q, Relation.TransGen FullBeta (app Z M0) Q ∧ FullEtaStar Q P := by
  rcases hbeta with ( _ | _ | _ | _ );
  · rcases ‹_› with ( _ | _ | _ | _ );
    rcases ‹Beta _ _› with ( _ | _ | _ | _ );
    rename_i k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆;
    refine' ⟨ _, Relation.TransGen.single ( Xi.base ( Beta.beta hZ ( FullEta.lc_left he ) ) ), _ ⟩;
    apply_rules [ FullEtaStar.open_arg ];
    exact .single he;
  · obtain ⟨ Q, hQ₁, hQ₂ ⟩ := ih M0 ( by
      exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ) N0 _ he ‹_›;
    exact ⟨ _, fullBetaTrans_appL hZ hQ₁, FullEtaStar.appL hZ hQ₂ ⟩;
  · rename_i N hN hN';
    refine' ⟨ _, fullBetaTrans_appR ( FullEta.lc_left he ) _, FullEtaStar.appL ( FullBeta.lc_right hN ) _ ⟩;
    · exact .single hN;
    · exact .single he

/-
The β-redex-creation subcase where the operator η-reduces (by a top η-redex)
to an abstraction.
-/
theorem takaP_appR_redex {W Z : Term Var} (hZ : LC Z) (hW : LC (abs W)) :
    ∃ Q, Relation.TransGen FullBeta
        (app (abs (app (abs W) (bvar 0))) Z) Q ∧ FullEtaStar Q (W ^ Z) := by
  -- Prove that `LC (abs (app (abs W) (bvar 0)))` by showing it is locally closed.
  have hLC : LC (Term.abs (Term.app (Term.abs W) (Term.bvar 0))) := by
    apply Term.LC.abs;
    intro x hx;
    convert Term.LC.app ?_ ( Term.LC.fvar x ) using 1;
    convert hW using 1;
    convert Term.openRec_lc hW 0 ( fvar x ) using 1;
    exact ∅
  exact (by
  refine' ⟨ W ^ Z, _, _ ⟩;
  · refine' .head _ ( .single _ );
    exact Xi.base ( Beta.beta hLC hZ );
    -- By definition of `openRec`, we have `openRec 0 Z (abs W) = abs W`.
    have h_openRec : openRec 0 Z (abs W) = abs W := by
      grind +suggestions;
    convert Xi.base ( Beta.beta hW hZ ) using 1;
    exact congr_arg₂ _ h_openRec rfl;
  · exact .refl)

/-
The β-redex-creation subcase where the operator is an abstraction whose body
η-reduces.
-/
theorem takaP_appR_create {M0b W Z : Term Var} (xs : Finset Var) (hZ : LC Z)
    (hM0 : LC (abs M0b))
    (hbody : ∀ x ∉ xs, FullEta (M0b ^ fvar x) (W ^ fvar x)) :
    ∃ Q, Relation.TransGen FullBeta (app (abs M0b) Z) Q ∧ FullEtaStar Q (W ^ Z) := by
  use M0b ^ Z;
  constructor;
  · exact .single ( Xi.base ( Beta.beta hM0 hZ ) );
  · convert FullEtaStar.open_body xs ( fun x hx => Relation.ReflTransGen.single ( hbody x hx ) ) hZ using 1

/-
η-step in the operator of an application (includes β-redex creation).
-/
theorem takaP_appR {M0 Z N0 P : Term Var}
    (ih : ∀ (M' : Term Var), size M' < size (app M0 Z) → TakaPlusProp M')
    (hZ : LC Z) (he : FullEta M0 N0) (hbeta : FullBeta (app N0 Z) P) :
    ∃ Q, Relation.TransGen FullBeta (app M0 Z) Q ∧ FullEtaStar Q P := by
  by_contra h_contra;
  cases' hbeta with hbeta hbeta;
  · cases' ‹Beta _ _› with hW hZ' hP;
    cases' he with he he;
    · cases ‹Eta M0 hW.abs›;
      exact h_contra <| takaP_appR_redex hZ hP;
    · rename_i k hk;
      exact h_contra <| by have := takaP_appR_create ‹_› hZ ( FullEta.lc_left <| show FullEta ( k.abs ) ( hW.abs ) from Xi.abs _ hk ) hk; tauto;
  · rename_i N hN hN';
    refine' h_contra ⟨ _, fullBetaTrans_appL _ ( Relation.TransGen.single hN' ), _ ⟩;
    · have := FullEta.lc_left he; aesop;
    · grind +suggestions;
  · rename_i N hN hZ';
    obtain ⟨w, hw1, hw2⟩ : ∃ w, Relation.TransGen FullBeta M0 w ∧ FullEtaStar w N := by
      exact ih M0 ( by simp +decide [ Term.size ] ) N0 N he ( by tauto );
    refine' h_contra ⟨ _, fullBetaTrans_appR hZ' hw1, FullEtaStar.appR hZ' hw2 ⟩

/-
Witness packaging for the abstraction case (β side via closing).
-/
theorem exists_Q_abs_plus {M0 P0 W : Term Var} (z : Var)
    (hz0 : z ∉ fv M0) (hzP : z ∉ fv P0)
    (hbeta : Relation.TransGen FullBeta (M0 ^ fvar z) W)
    (heta : FullEtaStar W (P0 ^ fvar z)) :
    ∃ Q, Relation.TransGen FullBeta (Term.abs M0) Q ∧ FullEtaStar Q (Term.abs P0) := by
  -- By `fullBetaTrans_abs_close z hbeta`, we get `Relation.TransGen FullBeta (abs (closeRec 0 z (M0 ^ fvar z))) (abs (closeRec 0 z W))`.
  have h_trans : Relation.TransGen FullBeta (abs (closeRec 0 z (M0 ^ fvar z))) (abs (closeRec 0 z W)) := by
    convert fullBetaTrans_abs_close z hbeta using 1;
  refine' ⟨ _, _, _ ⟩;
  exact ( closeRec 0 z W ).abs;
  · convert h_trans using 1;
    rw [ show closeRec 0 z ( M0 ^ fvar z ) = M0 from ?_ ];
    convert Term.close_open hz0 0 using 1;
  · convert XiStar.abs_close ( fun _ _ => Eta.regular ) ( fun _ _ hab y w hw => Eta.subst hab y hw ) z heta using 1;
    exact congr_arg _ ( by exact Eq.symm ( Term.close_open hzP 0 ) )

/-
η-step under a binder.
-/
theorem takaP_abs {M0 N0 P : Term Var} (xs : Finset Var)
    (ih : ∀ (M' : Term Var), size M' < size (abs M0) → TakaPlusProp M')
    (hbody : ∀ x ∉ xs, FullEta (M0 ^ fvar x) (N0 ^ fvar x))
    (hbeta : FullBeta (abs N0) P) :
    ∃ Q, Relation.TransGen FullBeta (abs M0) Q ∧ FullEtaStar Q P := by
  cases' hbeta with N0' hN0';
  · cases' ‹Beta N0.abs P› with N0' hN0';
  · obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ xs ∪ ‹Finset Var› ∪ fv M0 ∪ fv ‹_› := by
      exact Finset.exists_notMem _;
    have := ih ( M0 ^ fvar z ) ?_ ( N0 ^ fvar z ) ( ‹_› ^ fvar z ) ( hbody z ?_ ) ( ‹∀ x ∉ _, Xi Beta ( N0 ^ fvar x ) ( _ ^ fvar x ) › z ?_ );
    · exact exists_Q_abs_plus z ( by aesop ) ( by aesop ) this.choose_spec.1 this.choose_spec.2;
    · simp +decide [ Term.size ];
      convert Term.size_openRec_fvar 0 z M0 |> le_of_eq;
    · grind;
    · grind

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
    AbstractPostpone.StrongLocal (FullBeta (Var := Var)) (FullEta (Var := Var)) :=
  fun _ _ _ he hbeta => eta_beta_local _ _ _ he hbeta

/-
Weak commutation of full β and full η (derived from η-postponement via the
parallel-β local lemma).
-/
theorem weakCommute_fullBeta_fullEta :
    AbstractPostpone.WeakCommute (FullBeta (Var := Var)) (FullEta (Var := Var)) := by
  intro p q r hpq hqr;
  obtain ⟨ s, hs ⟩ := AbstractPostpone.postpone ( localPostpone_parBeta_fullEta ) ( by
    convert hpq.mono _ |> Relation.ReflTransGen.trans <| hqr.mono _ using 1;
    · exact fun a b hab => Or.inr hab;
    · exact fun a b hab => Or.inl <| ParBeta.of_FullBeta hab : Relation.ReflTransGen ( fun a b => ParBeta a b ∨ FullEta a b ) p r );
  exact ⟨ s, parBetaStar_toFullBetaStar hs.1, hs.2 ⟩

/-! ## Main theorem -/

/-- **Strong η-postponement (single β-step).**  If `t ⟶η* t'` and `t' ⟶β t''`,
then there is `y` with a non-empty β-reduction `t ⟶β⁺ y` and `y ⟶η* t''`. -/
theorem eta_beta_postpone {t t' t'' : Term Var}
    (htt' : FullEtaStar t t') (ht'' : FullBeta t' t'') :
    ∃ y, Relation.TransGen FullBeta t y ∧ FullEtaStar y t'' := by
  exact AbstractPostpone.star_over_plus weakCommute_fullBeta_fullEta
    strongLocal_fullBeta_fullEta htt' (Relation.TransGen.single ht'')

end LambdaLN