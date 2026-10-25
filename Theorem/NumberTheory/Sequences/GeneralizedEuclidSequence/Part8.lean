/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part8
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

theorem seqA_eq (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i t : ℕ)
    (ht : i + 1 ≤ t) : seqA P hP i = eVal (chainL P hP t) i := by
  change eVal (chainL P hP (i + 1)) i = _
  exact chainL_eval_stable P hP i (i + 1) t
    (by have h := chainL_len P hP (i + 1); omega) ht

theorem seqA_prime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i : ℕ) :
    (seqA P hP i).Prime := by
  have hlen : i < (chainL P hP (i + 1)).length := by
    have h := chainL_len P hP (i + 1); omega
  rw [seqA_eq P hP i (i + 1) le_rfl, eVal_lt _ _ hlen]
  exact (chainL_good P hP (i + 1)).2.2.1 _ (List.getElem_mem hlen)

theorem seqA_injective (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (seqA P hP) := by
  intro i j hij
  rcases le_total i j with hle | hle
  · have hi : i < (chainL P hP (j + 1)).length := by
      have h := chainL_len P hP (j + 1); omega
    have hj : j < (chainL P hP (j + 1)).length := by
      have h := chainL_len P hP (j + 1); omega
    have e1 := seqA_eq P hP i (j + 1) (by omega)
    have e2 := seqA_eq P hP j (j + 1) le_rfl
    rw [eVal_lt _ _ hi] at e1
    rw [eVal_lt _ _ hj] at e2
    have heq : (chainL P hP (j + 1))[i] = (chainL P hP (j + 1))[j] := by
      rw [← e1, ← e2]; exact hij
    exact (List.Nodup.getElem_inj_iff (chainL_good P hP (j + 1)).2.1).mp heq
  · have hi : i < (chainL P hP (i + 1)).length := by
      have h := chainL_len P hP (i + 1); omega
    have hj : j < (chainL P hP (i + 1)).length := by
      have h := chainL_len P hP (i + 1); omega
    have e1 := seqA_eq P hP i (i + 1) le_rfl
    have e2 := seqA_eq P hP j (i + 1) (by omega)
    rw [eVal_lt _ _ hi] at e1
    rw [eVal_lt _ _ hj] at e2
    have heq : (chainL P hP (i + 1))[j] = (chainL P hP (i + 1))[i] := by
      rw [← e1, ← e2]; exact hij.symm
    exact ((List.Nodup.getElem_inj_iff (chainL_good P hP (i + 1)).2.1).mp heq).symm

theorem seqA_mem_seed (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i : ℕ)
    (hi : i < P.card) : seqA P hP i ∈ P := by
  have hlen0 : i < P.toList.length := by rwa [Finset.length_toList]
  have h0 : chainL P hP 0 = P.toList := rfl
  have hpre : P.toList <+: chainL P hP (i + 1) := by
    have h := chainL_prefix_le P hP 0 (i + 1) (Nat.zero_le _)
    rwa [h0] at h
  have e1 := seqA_eq P hP i (i + 1) le_rfl
  have e2 := eVal_prefix P.toList (chainL P hP (i + 1)) hpre i hlen0
  rw [eVal_lt P.toList i hlen0] at e2
  rw [e1, ← e2]
  exact Finset.mem_toList.mp (List.getElem_mem hlen0)

theorem seqA_cover_seed (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (p : ℕ)
    (hp : p ∈ P) : ∃ i < P.card, seqA P hP i = p := by
  have hmem : p ∈ P.toList := Finset.mem_toList.mpr hp
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  have hiC : i < P.card := by
    have h := Finset.length_toList P; omega
  refine ⟨i, hiC, ?_⟩
  have h0 : chainL P hP 0 = P.toList := rfl
  have hpre : P.toList <+: chainL P hP (i + 1) := by
    have h := chainL_prefix_le P hP 0 (i + 1) (Nat.zero_le _)
    rwa [h0] at h
  have e1 := seqA_eq P hP i (i + 1) le_rfl
  have e2 := eVal_prefix P.toList (chainL P hP (i + 1)) hpre i hi
  have e3 := eVal_lt P.toList i hi
  rw [e1, ← e2, e3, heq]

theorem seqA_step (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ)
    (hn : P.card ≤ n) :
    ∃ I : Finset ℕ, I ⊆ Finset.range n ∧
      seqA P hP n ∣ (∏ i ∈ I, seqA P hP i) + ∏ i ∈ (Finset.range n \ I), seqA P hP i := by
  have hlen : n < (chainL P hP (n + 1)).length := by
    have h := chainL_len P hP (n + 1); omega
  obtain ⟨I, hI, hdvd⟩ := (chainL_good P hP (n + 1)).2.2.2 n hn hlen
  refine ⟨I, hI, ?_⟩
  have han : seqA P hP n = (chainL P hP (n + 1))[n] := by
    rw [seqA_eq P hP n (n + 1) le_rfl]
    exact eVal_lt _ _ hlen
  have hval : ∀ i ∈ I, seqA P hP i = eVal (chainL P hP (n + 1)) i := by
    intro i hi
    have hi' : i < n := by
      have h := hI hi
      rwa [Finset.mem_range] at h
    exact seqA_eq P hP i (n + 1) (by omega)
  have hval2 : ∀ i ∈ Finset.range n \ I, seqA P hP i = eVal (chainL P hP (n + 1)) i := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range] at hi
    exact seqA_eq P hP i (n + 1) (by omega)
  rw [han, Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2]
  exact hdvd

theorem chainL_qprop (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    (sInf {p | p.Prime ∧ p ∉ chainL P hP s}).Prime ∧
      sInf {p | p.Prime ∧ p ∉ chainL P hP s} ∉ chainL P hP s := by
  have hne : {p | p.Prime ∧ p ∉ chainL P hP s}.Nonempty := by
    obtain ⟨r, hrp, hrn⟩ := exists_fresh _ (chainL_good P hP s).2.1 (chainL_good P hP s).2.2.1
    exact ⟨r, hrp, hrn⟩
  exact Nat.sInf_mem hne

theorem chainL_qstrict (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP s} <
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := by
  have hmem : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ∈ chainL P hP (s + 1) :=
    (chainL_spec P hP s).2.2
  have hnot := (chainL_qprop P hP (s + 1)).2
  have hne : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ≠
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := fun h => hnot (h ▸ hmem)
  have hle : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ≤
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have hnotin : sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} ∉ chainL P hP s := by
      intro hin
      exact hnot (prefix_mem (chainL_step P hP s) _ hin)
    have hmem2 : sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} ∈
        {p | p.Prime ∧ p ∉ chainL P hP s} :=
      ⟨(chainL_qprop P hP (s + 1)).1, hnotin⟩
    have hle2 := Nat.sInf_le hmem2
    omega
  exact lt_of_le_of_ne hle hne

theorem chainL_qgrowth (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP 0} + s ≤
      sInf {p | p.Prime ∧ p ∉ chainL P hP s} := by
  induction s with
  | zero => exact Nat.le_refl _
  | succ s ih =>
    have hlt := chainL_qstrict P hP s
    omega

theorem chainL_cover (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (q : ℕ)
    (hq : q.Prime) : q ∈ chainL P hP (q + 1) := by
  by_contra hnin
  have hmem : q ∈ {p | p.Prime ∧ p ∉ chainL P hP (q + 1)} := ⟨hq, hnin⟩
  have hle := Nat.sInf_le hmem
  have hg := chainL_qgrowth P hP (q + 1)
  omega

theorem seqA_cover_all (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (p : ℕ)
    (hp : p.Prime) : ∃ i, seqA P hP i = p := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (chainL_cover P hP p hp)
  refine ⟨i, ?_⟩
  have h3 : seqA P hP i = eVal (chainL P hP (i + 1)) i := rfl
  have h2 : eVal (chainL P hP (p + 1)) i = p := by
    rw [eVal_lt _ _ hi]; exact heq
  rcases le_total (i + 1) (p + 1) with hle | hle
  · have h1 : eVal (chainL P hP (i + 1)) i = eVal (chainL P hP (p + 1)) i :=
      eVal_prefix _ _ (chainL_prefix_le P hP (i + 1) (p + 1) hle) i
        (by have h := chainL_len P hP (i + 1); omega)
    rw [h3, h1, h2]
  · have h1 : eVal (chainL P hP (p + 1)) i = eVal (chainL P hP (i + 1)) i :=
      eVal_prefix _ _ (chainL_prefix_le P hP (p + 1) (i + 1) hle) i hi
    rw [h3, ← h1, h2]

/--
For any finite set `P` of primes there is a generalized Euclid sequence
with seed `P` (each new term a prime divisor of
`∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` for some `I`) containing every prime.

Source: Andrew R. Booker, "A Variant of the Euclid-Mullin Sequence
Containing Every Prime," Journal of Integer Sequences 19 (2016),
Article 16.6.4, Theorem (label t:main), lines 132–136,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Booker/book3.tex

The source's construction: for primes `p_1, …, p_k` and any
`I ⊆ {1, …, k}`, `N_I = ∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` is coprime to
the previous product, so a prime divisor of `N_I` is always new; the
sequence is zero-indexed here with the first `P.card` terms enumerating
the seed. This is an existence claim over all choices of `I` and prime
divisor, unlike the open Euclid–Mullin conjecture about one specific
sequence.

Proves `Wanted` entry `generalized_euclid_sequence_contains_every_prime`.

Proof: Booker's residue-set route, with an elementary squarefree count in place of Rogers'
density bound and Jacobi-sum character-sum bounds in place of the Hasse and Weil bounds.
-/
theorem generalized_euclid_sequence_contains_every_prime
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∃ a : ℕ → ℕ, (∀ i, Nat.Prime (a i)) ∧ Function.Injective a ∧
      (∀ i < P.card, a i ∈ P) ∧ (∀ p ∈ P, ∃ i < P.card, a i = p) ∧
      (∀ n, P.card ≤ n → ∃ I : Finset ℕ, I ⊆ Finset.range n ∧
        a n ∣ (∏ i ∈ I, a i) + ∏ i ∈ (Finset.range n \ I), a i) ∧
      (∀ p, Nat.Prime p → ∃ i, a i = p) := by
  exact ⟨seqA P hP, seqA_prime P hP, seqA_injective P hP, seqA_mem_seed P hP,
    seqA_cover_seed P hP, seqA_step P hP, seqA_cover_all P hP⟩

end MetaMathlibExt
