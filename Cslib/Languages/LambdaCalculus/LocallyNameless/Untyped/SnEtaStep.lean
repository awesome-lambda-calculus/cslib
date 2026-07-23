import RequestProject.TakahashiSupport

/-!
# η-expansion preserves β-strong-normalisation (`sn_eta_step`)

This file formalises the paper proof in `sn_eta_step_proof.md`:

  **If `t ⟶η t'` (a single full η-step) and `t'` is β-strongly-normalising,
  then `t` is β-strongly-normalising.**

("β-strongly-normalising" is `Acc (flip FullBeta)`, i.e. accessibility for single
β-steps.)

The proof follows Takahashi-style **parallel η-reduction with an explicit
`Eta`-count**.  We define `ParEtaC n M N` = "`M` reduces to `N` by a parallel
η-derivation containing exactly `n` contractions of an η-redex".  The three
ingredients are:

* `parEtaC_of_fullEta` (Fact 2.1): a single η-step gives a count-`1` derivation;
* `interaction` (the Interaction Lemma): a single β-step out of `t` either
  reflects to a genuine β-step out of `t'` (keeping some parallel η-derivation),
  or is *absorbed*, landing back on `t'` with a **strictly smaller** count;
* `sn_transfer` (the generalized SN-transfer theorem): lexicographic induction on
  `(β-accessibility rank of t', count n)`.
-/

open scoped Classical

universe u

namespace LambdaLN

open Term

variable {Var : Type u} [Infinite Var]

/-- **Parallel η-reduction with `Eta`-count** `ParEtaC n M N`: `M` reduces to `N`
by a parallel η-derivation whose number of η-contractions is exactly `n`. -/
inductive ParEtaC : ℕ → Term Var → Term Var → Prop
  /-- (η1) A free variable reduces to itself, count `0`. -/
  | fvar (x : Var) : ParEtaC 0 (Term.fvar x) (Term.fvar x)
  /-- (η3) Congruence for application; counts add. -/
  | app {a b : ℕ} {M M' N N' : Term Var} :
      ParEtaC a M M' → ParEtaC b N N' → ParEtaC (a + b) (Term.app M N) (Term.app M' N')
  /-- (η2) Congruence for abstraction (cofinite quantification); count preserved. -/
  | abs (xs : Finset Var) {a : ℕ} {M M' : Term Var} :
      (∀ x ∉ xs, ParEtaC a (M ^ Term.fvar x) (M' ^ Term.fvar x)) →
        ParEtaC a (Term.abs M) (Term.abs M')
  /-- (η4) Parallel contraction of an η-redex `λz.(M z) ⟹ M'`; count `+1`. -/
  | eta {a : ℕ} {M M' : Term Var} :
      LC M → ParEtaC a M M' → ParEtaC (a + 1) (Term.abs (Term.app M (Term.bvar 0))) M'

/-- Opening the η-redex body `app M (bvar 0)` of a locally closed `M`. -/
theorem openRec_app_bvar_lc {M : Term Var} (hM : LC M) (x : Var) :
    (Term.app M (Term.bvar 0)) ^ Term.fvar x = Term.app M (Term.fvar x) := by
  show Term.app (openRec 0 (Term.fvar x) M) (openRec 0 (Term.fvar x) (Term.bvar 0)) = _
  rw [openRec_lc hM]; rfl

/-- `ParEtaC` relates locally closed terms. -/
theorem ParEtaC.regular {n : ℕ} {M N : Term Var} (h : ParEtaC n M N) : LC M ∧ LC N := by
  induction h with
  | fvar x => exact ⟨LC.fvar x, LC.fvar x⟩
  | app _ _ ihM ihN => exact ⟨LC.app ihM.1 ihN.1, LC.app ihM.2 ihN.2⟩
  | abs xs _ ih =>
      exact ⟨LC.abs xs _ (fun x hx => (ih x hx).1), LC.abs xs _ (fun x hx => (ih x hx).2)⟩
  | @eta a M M' hM hMM' ih =>
      refine ⟨LC.abs (∅ : Finset Var) _ (fun y _ => ?_), ih.2⟩
      rw [openRec_app_bvar_lc hM]
      exact LC.app hM (LC.fvar y)

omit [Infinite Var] in
/-- `ParEtaC` is reflexive at count `0` on locally closed terms. -/
theorem ParEtaC.refl {M : Term Var} (h : LC M) : ParEtaC 0 M M := by
  induction' n : M.size using Nat.strong_induction_on with n ih generalizing M;
  match h with
  | LC.fvar x => simp +arith [Term.size] at n; exact ParEtaC.fvar x
  | LC.app h₁ h₂ =>
      simp +arith [Term.size] at n
      exact ParEtaC.app (ih _ (by linarith) h₁ rfl) (ih _ (by linarith) h₂ rfl)
  | LC.abs xs t ht =>
      simp +arith [Term.size] at n
      exact ParEtaC.abs xs (fun x hx => ih _ (by rw [size_open_fvar]; linarith) (ht x hx) rfl)

omit [Infinite Var] in
/-- **Fact 2.1.** A single full η-step is a parallel η-derivation of count `1`. -/
theorem parEtaC_of_fullEta {t t' : Term Var} (h : FullEta t t') : ParEtaC 1 t t' := by
  induction h with
  | base hEta =>
      cases hEta with
      | eta hLC => exact ParEtaC.eta hLC (ParEtaC.refl hLC)
  | appL hLC ih hih =>
      have hZ : ParEtaC 0 _ _ := ParEtaC.refl hLC
      exact ParEtaC.app hZ hih
  | appR hLC ih hih =>
      have hZ : ParEtaC 0 _ _ := ParEtaC.refl hLC
      exact ParEtaC.app hih hZ
  | abs k hbody ih =>
      exact ParEtaC.abs k ih

/-- **Renaming preserves the count.** Substituting one free variable for another
in a `ParEtaC` derivation preserves the derivation and its count. -/
theorem ParEtaC.rename {n : ℕ} {A B : Term Var} (h : ParEtaC n A B) (x y : Var) :
    ParEtaC n (subst x (Term.fvar y) A) (subst x (Term.fvar y) B) := by
  induction h with
  | fvar z =>
      by_cases hz : z = x
      · subst hz; simp only [subst]; exact ParEtaC.fvar y
      · simp only [subst, if_neg hz]; exact ParEtaC.fvar z
  | app hM hN ihM ihN => simp only [subst]; exact ParEtaC.app ihM ihN
  | @abs xs a M M' hbody ih =>
      simp only [subst]
      refine ParEtaC.abs (xs ∪ {x}) (fun z hz => ?_)
      have hzx : x ≠ z := fun h => hz (by simp [h])
      have hzxs : z ∉ xs := fun h => hz (by simp [h])
      have key := ih z hzxs
      rwa [subst_open_var hzx (LC.fvar y), subst_open_var hzx (LC.fvar y)] at key
  | @eta a M M' hM hMM' ih =>
      simp only [subst]
      exact ParEtaC.eta (subst_lc hM (LC.fvar y)) ih

/-- Build an abstraction derivation from a single fresh-variable body instance. -/
theorem ParEtaC.abs_of_open {m : ℕ} {N s' : Term Var} (x : Var)
    (hx : x ∉ fv N) (hx' : x ∉ fv s') (h : ParEtaC m (N ^ Term.fvar x) (s' ^ Term.fvar x)) :
    ParEtaC m (Term.abs N) (Term.abs s') := by
  refine ParEtaC.abs (fv N ∪ fv s') ?_
  intro y hy
  by_cases hyc : y = x
  · rw [hyc]; exact h
  · have hr := ParEtaC.rename h x y
    have eqN : N ^ Term.fvar y = subst x (Term.fvar y) (N ^ Term.fvar x) := by
      rw [Term.hpow_def, Term.hpow_def]
      rw [subst_openRec (LC.fvar y) 0 (Term.fvar x) N]
      rw [subst_fresh hx]
      simp +decide [subst]
    have eqN' : s' ^ Term.fvar y = subst x (Term.fvar y) (s' ^ Term.fvar x) := by
      rw [Term.hpow_def, Term.hpow_def]
      rw [subst_openRec (LC.fvar y) 0 (Term.fvar x) s']
      rw [subst_fresh hx']
      simp +decide [subst]
    rw [eqN, eqN']
    exact hr

/-- **Fact 2.3 (Substitutivity).** If `M ⟹η M'` and `N ⟹η N'`, then
`M[x:=N] ⟹η M'[x:=N']` (for some count `c`). -/
theorem ParEtaC.substC {a b : ℕ} {M M' N N' : Term Var} (x : Var)
    (hM : ParEtaC a M M') (hN : ParEtaC b N N') :
    ∃ c, ParEtaC c (subst x N M) (subst x N' M') := by
  induction hM generalizing N N' with
  | fvar y =>
      by_cases h : y = x
      · subst h; simpa [subst] using ⟨b, hN⟩
      · simp only [subst, if_neg h]; exact ⟨0, ParEtaC.fvar y⟩
  | app hM hN ihM ihN =>
      simp only [subst]
      obtain ⟨c1, hc1⟩ := ihM hN
      obtain ⟨c2, hc2⟩ := ihN hN
      exact ⟨c1 + c2, ParEtaC.app hc1 hc2⟩
  | @abs xs a M M' hbody ih =>
      simp only [subst]
      have hNreg := hN.regular
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
        (xs ∪ {x} ∪ (M.fv) ∪ (M'.fv) ∪ N.fv ∪ N'.fv)
      have hyxs : y ∉ xs := fun h => hy (by simp [h])
      have hyx : ¬y = x := fun h => hy (by simp [h])
      obtain ⟨c, hc⟩ := ih y hyxs hN
      use c
      apply abs_of_open y
      · intro H
        have := fv_subst_subset x N _ H
        simp_all [Finset.mem_union, Finset.mem_sdiff]
      · intro H
        have := fv_subst_subset x N' _ H
        simp_all [Finset.mem_union, Finset.mem_sdiff]
      · rw [subst_open_var (Ne.symm hyx) hNreg.1] at hc
        rw [subst_open_var (Ne.symm hyx) hNreg.2] at hc
        exact hc
  | @eta a M M' hM hMM' ih =>
      obtain ⟨c, hc⟩ := ih hN
      use c + 1
      have hsub : subst x N ((M.app (Term.bvar 0)).abs)
          = ((subst x N M).app (Term.bvar 0)).abs := by
        simp only [Term.subst]
      rw [hsub]
      exact ParEtaC.eta hc.regular.1 hc

/-- Opening form of substitutivity: from `abs M ⟹η abs M'` and `N ⟹η N'`, the
opened bodies satisfy `M^N ⟹η M'^N'` (for some count). -/
theorem ParEtaC.open_of_absBody {a b : ℕ} (xs : Finset Var) {M M' N N' : Term Var}
    (hbody : ∀ x ∉ xs, ParEtaC a (M ^ Term.fvar x) (M' ^ Term.fvar x))
    (hN : ParEtaC b N N') :
    ∃ c, ParEtaC c (M ^ N) (M' ^ N') := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (xs ∪ fv M ∪ fv M')
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨hxxs, hxM⟩, hxM'⟩ := hx
  obtain ⟨c, hc⟩ := ParEtaC.substC x (hbody x hxxs) hN
  refine ⟨c, ?_⟩
  rw [show M ^ N = subst x N (M ^ Term.fvar x) from subst_intro hxM,
      show M' ^ N' = subst x N' (M' ^ Term.fvar x) from subst_intro hxM']
  exact hc

omit [Infinite Var] in
/-- Opening by a fresh free variable is injective. -/
theorem open_fvar_inj {A B : Term Var} {x : Var} (hA : x ∉ fv A) (hB : x ∉ fv B)
    (h : A ^ Term.fvar x = B ^ Term.fvar x) : A = B := by
  have hcl : closeRec 0 x (A ^ Term.fvar x) = closeRec 0 x (B ^ Term.fvar x) := by rw [h]
  simp only [Term.hpow_def] at hcl
  rwa [Term.close_open hA, Term.close_open hB] at hcl

omit [Infinite Var] in
/-- `x` is not free in `closeRec k x t`. -/
theorem fv_closeRec_notMem (k : ℕ) (x : Var) (t : Term Var) : x ∉ fv (closeRec k x t) := by
  induction t generalizing k with
  | bvar i => simp [closeRec, fv]
  | fvar y =>
      by_cases h : y = x
      · simp [closeRec, fv, h]
      · simp only [closeRec, if_neg h, fv, Finset.mem_singleton]; exact fun e => h e.symm
  | abs t ih => simpa [closeRec, fv] using ih (k+1)
  | app t1 t2 ih1 ih2 =>
      simp only [closeRec, fv, Finset.mem_union]; push_neg; exact ⟨ih1 k, ih2 k⟩

omit [Infinite Var] in
/-- Substituting `x` by `fvar x` is the identity. -/
theorem subst_fvar_self (x : Var) (t : Term Var) : subst x (Term.fvar x) t = t := by
  induction t with
  | bvar i => rfl
  | fvar y => by_cases h : y = x <;> simp [subst, h]
  | abs t ih => simp [subst, ih]
  | app a b iha ihb => simp [subst, iha, ihb]

omit [Infinite Var] in
/-- The base β-rule does not create free variables. -/
theorem beta_fv_subset {a b : Term Var} (h : Beta a b) : fv b ⊆ fv a := by
  induction h with
  | beta hM hN => simp [Term.fv, Term.fv_openRec]

omit [Infinite Var] in
/-- Opening never drops existing free variables. -/
theorem fv_subset_openRec (k : ℕ) (u t : Term Var) : fv t ⊆ fv (openRec k u t) := by
  induction t generalizing k with
  | bvar i => simp [fv]
  | fvar y => simp [openRec, fv]
  | abs t ih => simpa [openRec, fv] using ih (k+1)
  | app t1 t2 ih1 ih2 =>
      intro y hy
      simp only [openRec, fv, Finset.mem_union] at hy ⊢
      exact hy.imp (fun h => ih1 k h) (fun h => ih2 k h)

/-- Full β-reduction does not create free variables (needs `Infinite Var` so the
ξ-rule's cofinite quantification is nonvacuous). -/
theorem fullBeta_fv_subset {a b : Term Var} (h : FullBeta a b) : fv b ⊆ fv a := by
  induction h with
  | base hb => exact beta_fv_subset hb
  | @appL Z M N hZ hxi ih =>
      intro y hy
      simp only [fv, Finset.mem_union] at hy ⊢
      exact hy.imp id (fun hh => ih hh)
  | @appR Z M N hZ hxi ih =>
      intro y hy
      simp only [fv, Finset.mem_union] at hy ⊢
      exact hy.imp (fun hh => ih hh) id
  | @abs xs M N hbody ih =>
      intro y hy
      simp only [fv] at hy ⊢
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (xs ∪ fv M ∪ fv N ∪ {y})
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
      obtain ⟨⟨⟨hzxs, hzM⟩, hzN⟩, hzy⟩ := hz
      have hyNz : y ∈ fv (N ^ Term.fvar z) := fv_subset_openRec 0 (Term.fvar z) N hy
      have hyMz : y ∈ fv (M ^ Term.fvar z) := ih z hzxs hyNz
      have hsub := fv_openRec 0 (Term.fvar z) M hyMz
      simp only [fv, Finset.mem_union, Finset.mem_singleton] at hsub
      rcases hsub with h1 | h1
      · exact h1
      · exact absurd h1.symm hzy

/-- The conclusion of the Interaction Lemma at a fixed source term `t`. -/
def InteractionAt (t : Term Var) : Prop :=
  ∀ {n : ℕ} {t' s : Term Var}, ParEtaC n t t' → FullBeta t s →
    (∃ s' m, ParEtaC m s s' ∧ FullBeta t' s') ∨ (∃ m, m < n ∧ ParEtaC m s t')

/-- **The Interaction Lemma for an abstraction source** `abs M0`.  This is the
case of `interaction_step` where `t = abs M0`; it is factored out because it
requires two sub-analyses (the parallel derivation contracts the abstraction by
congruence, or by an outer η-redex). -/
theorem interaction_abs {M0 : Term Var}
    (IH : ∀ u : Term Var, size u < size (Term.abs M0) → InteractionAt u) :
    InteractionAt (Term.abs M0) := by
  intro n t' s hp hb
  cases hb with
  | base hβ => cases hβ
  | @abs xs _ N0 hbodystep =>
    -- s = abs N0, hbodystep : ∀ x ∉ xs, FullBeta (M0^x) (N0^x)
    cases hp with
    | abs ys hbody =>
      rename_i M0'
      -- t' = abs M0', hbody : ∀ x ∉ ys, ParEtaC n (M0^x) (M0'^x)
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
        (xs ∪ ys ∪ fv M0 ∪ fv M0' ∪ fv N0)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨⟨⟨⟨hxxs, hxys⟩, hxM0⟩, hxM0'⟩, hxN0⟩ := hx
      have hsz : size (M0 ^ Term.fvar x) < size (Term.abs M0) := by
        rw [size_open_fvar]; have : size (Term.abs M0) = size M0 + 1 := rfl; omega
      rcases IH (M0 ^ Term.fvar x) hsz (hbody x hxys) (hbodystep x hxxs) with
        ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · refine Or.inl ⟨Term.abs (closeRec 0 x s''), m, ?_, ?_⟩
        · apply ParEtaC.abs_of_open x hxN0 (fv_closeRec_notMem 0 x s'')
          have hopen : (closeRec 0 x s'') ^ Term.fvar x = s'' := by
            rw [Term.hpow_def, Term.open_close_lc (ParEtaC.regular hpar).2 x, subst_fvar_self]
          rw [hopen]; exact hpar
        · have hclose := Xi.abs_close (fun _ _ => Beta.regular)
            (fun _ _ hab yv wv hw => Beta.subst hab yv hw) x hbeta
          simp only [Term.hpow_def] at hclose
          rw [Term.close_open hxM0'] at hclose
          exact hclose
      · exact Or.inr ⟨m, hm, ParEtaC.abs_of_open x hxN0 hxM0' hpar⟩
    | @eta a2 P _ hP hPF =>
      -- M0 = app P (bvar 0), n = a2 + 1, hPF : ParEtaC a2 P t'
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (xs ∪ fv P ∪ fv N0 ∪ fv t')
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨⟨⟨hxxs, hxP⟩, hxN0⟩, hxt'⟩ := hx
      have hPx : (Term.app P (Term.bvar 0)) ^ Term.fvar x = Term.app P (Term.fvar x) :=
        openRec_app_bvar_lc hP x
      have hstepx : FullBeta (Term.app P (Term.fvar x)) (N0 ^ Term.fvar x) := by
        have h := hbodystep x hxxs; rwa [hPx] at h
      generalize hw : N0 ^ Term.fvar x = w at hstepx
      cases hstepx with
      | base hβ =>
        cases hβ with
        | @beta Q Narg hQ hNarg =>
          -- P = abs Q, Narg = fvar x, w = Q ^ fvar x, hw : N0^x = Q^x
          have hxQ : x ∉ fv Q := hxP
          have hN0Q : N0 = Q := open_fvar_inj hxN0 hxQ hw
          exact Or.inr ⟨a2, by omega, by rw [hN0Q]; exact hPF⟩
      | @appL Z M N hZ hxi =>
        cases hxi with | base hb2 => cases hb2
      | @appR Z M N hZ hxi =>
        -- M = P, Z = fvar x; hxi : FullBeta P N; w = app N (fvar x)
        have hPsLC : LC N := FullBeta.lc_right hxi
        have hxN : x ∉ fv N := fun h => hxP (fullBeta_fv_subset hxi h)
        have hNe : N0 = Term.app N (Term.bvar 0) := by
          apply open_fvar_inj hxN0 (by simp [fv, hxN])
          rw [hw, openRec_app_bvar_lc hPsLC x]
        have hsizeP : size P < size (Term.abs (Term.app P (Term.bvar 0))) := by
          have : size (Term.abs (Term.app P (Term.bvar 0))) = size P + 3 := rfl
          omega
        rcases IH P hsizeP hPF hxi with ⟨s', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
        · exact Or.inl ⟨s', m + 1, by rw [hNe]; exact ParEtaC.eta hPsLC hpar, hbeta⟩
        · exact Or.inr ⟨m + 1, by omega, by rw [hNe]; exact ParEtaC.eta hPsLC hpar⟩

/-- **The Interaction Lemma, one step of the size-recursion.**  Assuming the
Interaction property holds for all strictly smaller terms, it holds at `t`. -/
theorem interaction_step {t : Term Var}
    (IH : ∀ u : Term Var, size u < size t → InteractionAt u) : InteractionAt t := by
  intro n t' s hp hb
  cases hb with
  | base hβ =>
    -- redex at the top: t = app (abs M) N, s = M ^ N
    cases hβ with
    | @beta M N hM hN =>
      cases hp with
      | @app a b _ F _ N' hf hn =>
        cases hf with
        | abs ys hbody =>
          -- t' = app (abs M') N' still a redex; genuine β-step on t'
          obtain ⟨c, hc⟩ := ParEtaC.open_of_absBody ys hbody hn
          exact Or.inl ⟨_, c, hc,
            Xi.base (Beta.beta (ParEtaC.regular (ParEtaC.abs ys hbody)).2 (ParEtaC.regular hn).2)⟩
        | @eta a2 P _ hP hPF =>
          -- M = app P (bvar 0); the β-step is absorbed by the η-redex
          have hs : (Term.app P (Term.bvar 0)) ^ N = Term.app P N := by
            show Term.app (openRec 0 N P) (openRec 0 N (Term.bvar 0)) = _
            rw [openRec_lc hP]; rfl
          refine Or.inr ⟨a2 + b, by omega, ?_⟩
          rw [hs]
          exact ParEtaC.app hPF hn
  | @appL Z M0 N0 hZ hstep =>
    cases hp with
    | @app a b _ Z' _ M0' hZ' hM0 =>
      have hsz : size M0 < size (Term.app Z M0) := by
        have : size (Term.app Z M0) = size Z + size M0 + 1 := rfl
        omega
      rcases IH M0 hsz hM0 hstep with ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · exact Or.inl ⟨_, a + m, ParEtaC.app hZ' hpar, Xi.appL (ParEtaC.regular hZ').2 hbeta⟩
      · exact Or.inr ⟨a + m, by omega, ParEtaC.app hZ' hpar⟩
  | @appR Z M0 N0 hZ hstep =>
    cases hp with
    | @app a b M0' _ _ Z' hM0 hZ' =>
      have hsz : size M0 < size (Term.app M0 Z) := by
        have : size (Term.app M0 Z) = size M0 + size Z + 1 := rfl
        omega
      rcases IH M0 hsz hM0 hstep with ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · exact Or.inl ⟨_, m + b, ParEtaC.app hpar hZ', Xi.appR (ParEtaC.regular hZ').2 hbeta⟩
      · exact Or.inr ⟨m + b, by omega, ParEtaC.app hpar hZ'⟩
  | @abs xs M0 N0 hbodystep =>
    exact interaction_abs IH hp (Xi.abs xs hbodystep)

/-- **The Interaction Lemma.** A single β-step `t ⟶β s` against a parallel
η-derivation `t ⟹η t'` either reflects to a genuine β-step `t' ⟶β s'` (with `s`
still parallel-η-reducing to `s'`), or is absorbed — landing back on `t'` with a
strictly smaller η-count. -/
theorem interaction {t : Term Var} : InteractionAt t := by
  have key : ∀ k (t : Term Var), size t = k → InteractionAt t := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro t ht
      exact interaction_step (fun u hu => ihk (size u) (ht ▸ hu) u rfl)
  intro n t' s hp hb
  exact key (size t) t rfl hp hb

/-- **Generalized SN-transfer theorem.**  If `t ⟹η t'` (parallel η, any count)
and `t'` is β-strongly-normalising, then so is `t`. -/
theorem sn_transfer {t t' : Term Var}
    (hacc : Acc (flip (FullBeta : Term Var → Term Var → Prop)) t')
    {n : ℕ} (hp : ParEtaC n t t') :
    Acc (flip (FullBeta : Term Var → Term Var → Prop)) t := by
  induction hacc generalizing t n with
  | intro c hc ih =>
      have key : ∀ n t, ParEtaC n t c →
          Acc (flip (FullBeta : Term Var → Term Var → Prop)) t := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihn =>
          intro t hp
          refine Acc.intro t (fun s hs => ?_)
          rcases interaction hp hs with ⟨s', m, hps', hb'⟩ | ⟨m, hm, hps⟩
          · exact ih s' hb' hps'
          · exact ihn m hm s hps
      exact key n t hp

/-- **η-expansion preserves β-strong-normalisation (single step).**  If
`t ⟶η t'` (one η-step) and `t'` is β-strongly-normalising, then so is `t`. -/
theorem sn_eta_step {t t' : Term Var} (h : FullEta t t')
    (hs : Acc (flip (FullBeta : Term Var → Term Var → Prop)) t') :
    Acc (flip (FullBeta : Term Var → Term Var → Prop)) t :=
  sn_transfer hs (parEtaC_of_fullEta h)

end LambdaLN
