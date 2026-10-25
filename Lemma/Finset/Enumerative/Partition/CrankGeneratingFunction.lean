import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part9
open MetaMathlibExt


namespace MetaMathlibExt.CrankNonneg

/--
[crk_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_lower {M : ℕ} (P : Nat.Partition M) :
  -((Multiset.count 1 P.parts : ℕ) : ℤ) ≤ partitionCrank P := by
  unfold partitionCrank
  split
  · next h => rw [h]; simp
  · next h =>
    have hnn : (0 : ℤ) ≤ (((P.parts.filter
      (fun i => Multiset.count 1 P.parts < i)).card : ℕ) : ℤ) := by
      exact_mod_cast Nat.zero_le _
    omega

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_nonneg_of_count_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_nonneg_of_count_eq_zero {M : ℕ} (P : Nat.Partition M)
  (h : Multiset.count 1 P.parts = 0) : 0 ≤ partitionCrank P := by
  unfold partitionCrank
  split
  · next _ => exact_mod_cast Nat.zero_le _
  · next hne => exact absurd h hne

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_count_le {M : ℕ} (P : Nat.Partition M) :
  Multiset.count 1 P.parts ≤ M := by
  have h1 : Multiset.count 1 P.parts ≤ Multiset.card P.parts :=
    Multiset.count_le_card 1 P.parts
  have h2 : Multiset.card P.parts ≤ M := by
    calc Multiset.card P.parts = Multiset.card P.parts • 1 := by simp
      _ ≤ P.parts.sum := Multiset.card_nsmul_le_sum (fun x hx => P.parts_pos hx)
      _ = M := P.parts_sum
  omega

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_add_card_highParts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_add_card_highParts (k L : ℕ) (hk : 1 ≤ k) :
  crankLeCount k (L + k) + Fintype.card { π : Nat.Partition L // highPartsCond k π } =
  Fintype.card (Nat.Partition L) := by
  have h1 := Fintype.card_subtype_compl
    (fun s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } =>
      partitionCrank s.1 ≤ -(k : ℤ))
  have h2 := Fintype.card_subtype_le
    (fun s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } =>
      partitionCrank s.1 ≤ -(k : ℤ))
  have hsplit : Fintype.card { Q : Nat.Partition (L + k) // partitionCrank Q ≤ -(k : ℤ) } +
    Fintype.card { π : Nat.Partition L // highPartsCond k π } =
    Fintype.card (Nat.Partition L) := by
    have h3 := Fintype.card_congr (crkAddOnes k L)
    rw [← Fintype.card_congr (crkEquivLe k L hk),
      ← Fintype.card_congr (crkEquivHigh k L hk)]
    omega
  unfold crankLeCount
  exact hsplit

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_card_highParts_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_card_highParts_eq (k L : ℕ) (hk : 1 ≤ k) :
  Fintype.card { π : Nat.Partition L // highPartsCond k π } = crankLeCount (k + 1) L := by
  unfold crankLeCount
  exact Fintype.card_congr (crkEquivPhiPsi k L hk)

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crkE_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crkE_zero (k : ℕ) : crkE k 0 = 0 := by
  unfold crkE
  simp

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crkE_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crkE_succ (k m : ℕ) (hk : 1 ≤ k) : crkE k (m + 1) = k + crkE (k + 1) m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht := Nat.triangle_succ (m + 1)
  unfold crkE
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ht ⊢
  rw [ht]
  have e1 : (m + 1) * j = m * j + j := by ring
  have e2 : m * (j + 1) = m * j + m := by ring
  omega

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crkE_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crkE_ge (k m : ℕ) (hk : 1 ≤ k) : m * k ≤ crkE k m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht := Nat.triangle_succ m
  unfold crkE
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ht ⊢
  have e : m * (j + 1) = m * j + m := by ring
  omega

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_alt_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_alt_lt (k M : ℕ) (hk : 1 ≤ k) (hM : M < k) :
  crankAltSum k M = (Fintype.card (Nat.Partition M) : ℤ) := by
  unfold crankAltSum
  rw [Finset.sum_eq_single 0]
  · simp only [crkE_zero, Nat.zero_le, ↓reduceIte, pow_zero, one_mul, Nat.sub_zero]
  · intro m _ hm0
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hge := crkE_ge k m hk
    have hk2 : k ≤ m * k := by
      have h := Nat.mul_le_mul hm1 (le_refl k)
      rwa [Nat.one_mul] at h
    have hneg : ¬ crkE k m ≤ M := by omega
    simp [hneg]
  · intro hcon
    exact absurd (Finset.mem_range.mpr (by omega : (0 : ℕ) < M + 1)) hcon

end MetaMathlibExt.CrankNonneg

namespace MetaMathlibExt.CrankNonneg

/--
[crk_alt_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crk_alt_add (k L : ℕ) (hk : 1 ≤ k) :
  crankAltSum k (L + k) =
  (Fintype.card (Nat.Partition (L + k)) : ℤ) - crankAltSum (k + 1) L := by
  have hterm : ∀ i : ℕ,
    (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
      (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0)
    = -(if crkE (k + 1) i ≤ L then (-1 : ℤ) ^ i *
      (Fintype.card (Nat.Partition (L - crkE (k + 1) i)) : ℤ) else 0) := by
    intro i
    by_cases hg : crkE (k + 1) i ≤ L
    · have e1 := crkE_succ k i hk
      have g1 : k + crkE (k + 1) i ≤ L + k := by omega
      have hsub : (L + k) - (k + crkE (k + 1) i) = L - crkE (k + 1) i := by omega
      have hpow : (-1 : ℤ) ^ (i + 1) = -(-1 : ℤ) ^ i := by
        rw [pow_succ]
        ring
      simp only [g1, hg, ↓reduceIte, crkE_succ k i hk, hsub, hpow, neg_mul]
    · have e1 := crkE_succ k i hk
      have g1 : ¬ crkE k (i + 1) ≤ L + k := by omega
      simp only [g1, hg, ↓reduceIte, neg_zero]
  have hvanish : (∑ m ∈ Finset.range (L + k),
    (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
      (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0))
    = (∑ m ∈ Finset.range (L + 1),
      (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
    have hsub : Finset.range (L + 1) ⊆ Finset.range (L + k) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hvsym : (∑ m ∈ Finset.range (L + 1),
      (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0))
      = (∑ m ∈ Finset.range (L + k),
        (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) :=
      Finset.sum_subset hsub (by
        intro x hxmem hxnot
        rw [Finset.mem_range] at hxmem hxnot
        have hge := crkE_ge (k + 1) x (by omega : 1 ≤ k + 1)
        have hx1 : x ≤ x * (k + 1) := by
          have h := Nat.mul_le_mul (le_refl x) (by omega : 1 ≤ k + 1)
          rwa [Nat.mul_one] at h
        have hneg : ¬ crkE (k + 1) x ≤ L := by omega
        simp [hneg])
    exact hvsym.symm
  have hmain : (∑ i ∈ Finset.range (L + k),
    (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
      (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0))
    = -(∑ m ∈ Finset.range (L + 1),
      (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
    calc (∑ i ∈ Finset.range (L + k), (if crkE k (i + 1) ≤ L + k then (-1:ℤ)^(i+1) *
      (Fintype.card (Nat.Partition (L + k - crkE k (i+1))) : ℤ) else 0))
      = ∑ m ∈ Finset.range (L + k), (-(if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
      _ = -(∑ m ∈ Finset.range (L + k), (if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
        simp only [Finset.sum_neg_distrib]
      _ = -(∑ m ∈ Finset.range (L + 1), (if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
        rw [hvanish]
  have hsplit : (∑ m ∈ Finset.range (L + k + 1),
    (if crkE k m ≤ L + k then (-1 : ℤ) ^ m *
      (Fintype.card (Nat.Partition (L + k - crkE k m)) : ℤ) else 0))
    = (∑ i ∈ Finset.range (L + k),
      (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
        (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0))
      + (if crkE k 0 ≤ L + k then (-1 : ℤ) ^ (0 : ℕ) *
        (Fintype.card (Nat.Partition (L + k - crkE k 0)) : ℤ) else 0) :=
    Finset.sum_range_succ' _ _
  unfold crankAltSum
  rw [hsplit]
  simp only [crkE_zero, Nat.zero_le, ↓reduceIte, pow_zero, one_mul, Nat.sub_zero]
  rw [hmain]
  ring

end MetaMathlibExt.CrankNonneg

/--
[crank_nonneg_partition_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean)
-/
@[path]
private lemma crank_nonneg_partition_count_eq
  {N : ℕ} :
-- imply
  Fintype.card { P : Nat.Partition N //
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
    else (((P.parts.filter
    (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
    - (Multiset.count 1 P.parts : ℤ)))}
    = ∑ n ∈ Finset.range (N + 1),
    (if (n + 1) * n / 2 ≤ N
    then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
    else 0) := by
-- proof
  apply MetaMathlibExt.crank_nonneg_partition_count N


-- created on 2026-10-20
-- updated on 2026-10-23
