/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part10


namespace MetaMathlibExt

namespace CrankNonneg

/-! ## Identification of the counting function -/

theorem crk_leCount_eq (M k : ℕ) (hk : 1 ≤ k) :
    (crankLeCount k M : ℤ) = (Fintype.card (Nat.Partition M) : ℤ) - crankAltSum k M := by
  have hR : ∀ (k L : ℕ), 1 ≤ k → crankLeCount k (L + k) + crankLeCount (k + 1) L
      = Fintype.card (Nat.Partition L) := by
    intro k L hk
    rw [← crk_card_highParts_eq k L hk]
    exact crk_add_card_highParts k L hk
  revert k hk
  induction M using Nat.strong_induction_on
  rename_i M ih
  intro k hk
  by_cases hMk : M < k
  · rw [crk_count_eq_zero_of_lt hk hMk, Nat.cast_zero, crk_alt_lt k M hk hMk]
    exact (sub_self _).symm
  · have hMk' : k ≤ M := le_of_not_gt hMk
    obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hMk'
    rw [Nat.add_comm k L]
    have hR' : (crankLeCount k (L + k) : ℤ) + (crankLeCount (k + 1) L : ℤ)
        = (Fintype.card (Nat.Partition L) : ℤ) := by
      exact_mod_cast hR k L hk
    have hIH : (crankLeCount (k + 1) L : ℤ)
        = (Fintype.card (Nat.Partition L) : ℤ) - crankAltSum (k + 1) L :=
      ih L (by omega) (k + 1) (by omega)
    have hA := crk_alt_add k L hk
    omega

end CrankNonneg

/-! # Non-negative crank generating function
-/

/--
Coefficient-wise form of the generating function for partitions with
non-negative crank: the number of partitions of `N` with crank `≥ 0` equals
`∑_n (-1)^n p(N - (n+1)n/2)`, the convolution of the partition numbers with
`(-1)^n` at the triangular numbers. The crank is the largest part when no
part equals `1`, else the number of parts exceeding the number of ones
minus the number of ones. The source notes this result is originally due
to Uncu. Verified at `N = 0..8`. Distinct from the same paper's quoted
Rogers–Ramanujan theorem.

Source: George E. Andrews and David Newman, "The Minimal Excludant in
Integer Partitions," Journal of Integer Sequences 23 (2020),
Article 20.2.3, Theorem (label Theorem1, equation 1.11), lines 161–165,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex

Proves `Wanted` entry `crank_nonneg_partition_count`.
-/
theorem crank_nonneg_partition_count
    (N : ℕ) :
    Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))}
    = ∑ n ∈ Finset.range (N + 1),
        (if (n + 1) * n / 2 ≤ N
          then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
          else 0) := by
  have h1 := Fintype.card_subtype_compl (fun P : Nat.Partition N =>
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
      else (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
        - (Multiset.count 1 P.parts : ℤ))))
  have h2 : Fintype.card { P : Nat.Partition N //
      ¬ 0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} = CrankNonneg.crankLeCount 1 N := by
    unfold CrankNonneg.crankLeCount
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro P
    unfold CrankNonneg.partitionCrank
    constructor <;> intro h <;> omega
  have hle := Fintype.card_subtype_le (fun P : Nat.Partition N =>
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
      else (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
        - (Multiset.count 1 P.parts : ℤ))))
  have hN : Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} + CrankNonneg.crankLeCount 1 N
      = Fintype.card (Nat.Partition N) := by
    omega
  have hsplit : ((Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} : ℕ) : ℤ)
      = (Fintype.card (Nat.Partition N) : ℤ) - (CrankNonneg.crankLeCount 1 N : ℤ) := by
    omega
  have h13 := CrankNonneg.crk_leCount_eq N 1 (by omega : 1 ≤ 1)
  have hSR : CrankNonneg.crankAltSum 1 N = ∑ n ∈ Finset.range (N + 1),
      (if (n + 1) * n / 2 ≤ N
        then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
        else 0) := by
    unfold CrankNonneg.crankAltSum
    apply Finset.sum_congr rfl
    intro m _
    have he : CrankNonneg.crkE 1 m = (m + 1) * m / 2 := by
      unfold CrankNonneg.crkE
      simp
    rw [he]
  omega

end MetaMathlibExt
