/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Def.Combinatorics.BellPermutationsSecondKind.Part5


namespace MetaMathlibExt

theorem fromSum_bij (n k : ℕ) : Function.Bijective (fromSum n k) := by
  constructor
  · rintro (⟨g, i⟩ | g) (⟨g', i'⟩ | g') hab
    · have hpair : (extPair_inl g i).1 = (extPair_inl g' i').1 := congrArg Subtype.val hab
      simp only [extPair_inl] at hpair
      rw [Prod.mk.injEq] at hpair
      have hg : g = g' := Subtype.ext hpair.1
      subst hg
      have hi : i = i' := Fin.ext (by have := congrArg Fin.val hpair.2; simpa using this)
      subst hi; rfl
    · exfalso
      have hpair : (extPair_inl g i).1 = (extPair_inr g').1 := congrArg Subtype.val hab
      simp only [extPair_inl, extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have e := congrArg numVals hpair.1
      rw [g.2.2, g'.2.2] at e; omega
    · exfalso
      have hpair : (extPair_inr g).1 = (extPair_inl g' i').1 := congrArg Subtype.val hab
      simp only [extPair_inl, extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have e := congrArg numVals hpair.1
      rw [g.2.2, g'.2.2] at e; omega
    · have hpair : (extPair_inr g).1 = (extPair_inr g').1 := congrArg Subtype.val hab
      simp only [extPair_inr] at hpair
      rw [Prod.mk.injEq] at hpair
      have hg : g = g' := Subtype.ext hpair.1
      subst hg; rfl
  · rintro ⟨⟨g, v⟩, hr, hle, heqk⟩
    have heqk' : numVals (ext g v) = k + 1 := heqk
    by_cases h : v.val < numVals g
    · have hgk : numVals g = k + 1 := (numVals_ext_lt hr v h).symm.trans heqk'
      have hvk : v.val < k + 1 := by omega
      refine ⟨Sum.inl (⟨g, hr, hgk⟩, ⟨v.val, hvk⟩), ?_⟩
      apply Subtype.ext
      simp only [fromSum, extPair_inl]
    · have heq : v.val = numVals g := le_antisymm hle (not_lt.mp h)
      have hgk : numVals g = k := by
        have h2 : numVals (ext g v) = numVals g + 1 := numVals_ext_eq hr v heq
        omega
      refine ⟨Sum.inr ⟨g, hr, hgk⟩, ?_⟩
      apply Subtype.ext
      simp only [fromSum, extPair_inr]
      exact Prod.ext_iff.mpr ⟨rfl, Fin.ext heq.symm⟩

theorem card_rec (n k : ℕ) :
    Nat.card (Asub (n+1) (k+1)) = (k+1) * Nat.card (Asub n (k+1)) + Nat.card (Asub n k) := by
  have e1 : Nat.card (Asub (n+1) (k+1)) = Nat.card (Psub n (k+1)) := Nat.card_congr (E1 n (k+1))
  have e2 : Nat.card (Psub n (k+1)) = Nat.card (((Asub n (k+1)) × Fin (k+1)) ⊕ Asub n k) :=
    (Nat.card_congr (Equiv.ofBijective _ (fromSum_bij n k))).symm
  rw [e1, e2, Nat.card_sum, Nat.card_prod]
  have hfin : Nat.card (Fin (k+1)) = k + 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hfin]; ring

theorem card_A_0_succ (k : ℕ) : Nat.card (Asub 0 (k+1)) = 0 := by
  have : IsEmpty (Asub 0 (k+1)) :=
    ⟨fun p => by obtain ⟨f, _, hn⟩ := p; have := numVals_le f; omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem rgf_count (n k : ℕ) : Nat.card (Asub n k) = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [card_A_0_0, Nat.stirlingSecond_zero]
    | succ k => rw [card_A_0_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => rw [card_A_succ_0, Nat.stirlingSecond_succ_zero]
    | succ k => rw [card_rec, ih (k+1), ih k, Nat.stirlingSecond_succ_succ]

/-! ## Gluing the three parts -/

theorem bellPerm_inj {n : ℕ} :
    Function.Injective (fun f : {g : Fin n → Fin n // IsRGF g} => bellPerm f.val) := by
  intro a b hab
  exact Subtype.ext (bellPerm_inj_subdiag (rgf_subdiag a.2) (rgf_subdiag b.2) hab)

theorem main (n k : ℕ) (_hn : 0 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k} =
      Nat.stirlingSecond n k := by
  rw [← rgf_count n k]
  refine (Nat.card_eq_of_bijective (f := fun p : {f : Fin n → Fin n // IsRGF f ∧ numVals f = k} =>
    (⟨bellPerm p.val, ⟨p.val, p.2.1, rfl, by rw [numWeak_bellPerm p.2.1, p.2.2]⟩⟩ :
      {σ : Equiv.Perm (Fin n) // ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k}))
          ?_).symm
  constructor
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    have h1 : bellPerm a.val = bellPerm b.val := hab
    have h2 := @bellPerm_inj n ⟨a.val, a.2.1⟩ ⟨b.val, b.2.1⟩ h1
    have h3 : a.val = b.val := by simpa using congrArg (·.val) h2
    exact Subtype.ext h3
  · rintro ⟨σ, f, hrgf, hbp, hweak⟩
    refine ⟨⟨f, hrgf, ?_⟩, ?_⟩
    · rw [← numWeak_bellPerm hrgf, hbp, hweak]
    · apply Subtype.ext; exact hbp

/--
The number of Bell permutations of the second kind over [n] with k weak
excedances equals the Stirling number of the second kind `S(n, k)`.

Source: Fufa Beyene, Jörgen Backelin, Roberto Mantaci, and Samuel A. Fufa,
"Set Partitions and Other Bell Number Enumerated Objects," Journal of Integer
Sequences 26 (2023), Article 23.1.8, Corollary (label corcycfx), item 1,
lines 283–290,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Beyene/beyene13.tex

Zero-based reading of the source's 1-based `[n]`: a restricted growth
function is one where every value below a prefix value has already appeared
in that prefix; the Bell permutation is the product, in increasing index
order, of the swaps `(i, f i)`; a weak excedance is an index with `i ≤ σ i`.

Proves `Wanted` entry `bell_perm_second_kind_weakExcedance_eq_stirlingSecond`.
-/
theorem bell_perm_second_kind_weakExcedance_eq_stirlingSecond
    (n k : ℕ) (hn : 0 < n) :
    let IsRGF : (Fin n → Fin n) → Prop :=
      fun f => ∀ i : Fin n, ∀ j : Fin n, j.val < (f i).val →
        ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = j;
    let bellPerm : (Fin n → Fin n) → Equiv.Perm (Fin n) :=
      fun f => ((List.finRange n).map fun i => Equiv.swap i (f i)).prod;
    let numWeak : Equiv.Perm (Fin n) → ℕ :=
      fun σ => Fintype.card {i : Fin n // i ≤ σ i};
    Nat.card {σ : Equiv.Perm (Fin n) //
      ∃ f : Fin n → Fin n, IsRGF f ∧ bellPerm f = σ ∧ numWeak σ = k} =
      Nat.stirlingSecond n k := by
  exact main n k hn

end MetaMathlibExt
