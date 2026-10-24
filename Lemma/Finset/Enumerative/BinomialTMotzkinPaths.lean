import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BinomialTMotzkinPaths
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[binomialTMotzkinCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_zero (t : ℕ) (h : ℤ) :
  binomialTMotzkinCount t 0 h = if h = 0 then 1 else 0 := by
  unfold binomialTMotzkinCount
  by_cases hh : h = 0
  · subst hh; simp
  · have : IsEmpty {p : Fin 0 → binomialTMotzkinStep t //
    (∀ m : Fin (0 + 1),
      0 ≤ ∑ i : Fin 0, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
    ∑ i : Fin 0, binomialTMotzkinHeight t (p i) = h} :=
    ⟨fun ⟨p, _, htot⟩ => by simp at htot; exact hh htot.symm⟩
    rw [Fintype.card_eq_zero]
    simp [hh]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_of_neg (t n : ℕ) (h : ℤ) (hh : h < 0) :
  binomialTMotzkinCount t n h = 0 := by
  unfold binomialTMotzkinCount
  have : IsEmpty {p : Fin n → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1),
      0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
      ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h} := by
    constructor
    rintro ⟨p, hpref, htot⟩
    have hlast := hpref (Fin.last n)
    have heq : (∑ i : Fin n, if i.1 < (Fin.last n).1 then binomialTMotzkinHeight t (p i) else 0)
      = ∑ i : Fin n, binomialTMotzkinHeight t (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.1 < (Fin.last n).1 := by
        rw [Fin.val_last]; exact i.isLt
      rw [ite_eq_left hi]
    rw [heq, htot] at hlast
    omega
  rw [Fintype.card_eq_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_of_gt (t n : ℕ) (h : ℤ) (hh : (n : ℤ) < h) :
  binomialTMotzkinCount t n h = 0 := by
  unfold binomialTMotzkinCount
  have : IsEmpty {p : Fin n → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1),
      0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
      ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h} := by
    constructor
    rintro ⟨p, _, htot⟩
    have hle : ∑ i : Fin n, binomialTMotzkinHeight t (p i) ≤ (n : ℤ) := by
      calc ∑ i : Fin n, binomialTMotzkinHeight t (p i)
        ≤ Finset.card (Finset.univ : Finset (Fin n)) • (1 : ℤ) := by
          apply Finset.sum_le_card_nsmul
          intro i _
          change (1 : ℤ) - ((p i).1 : ℤ) ≤ 1
          have hnn : (0 : ℤ) ≤ (((p i).1 : ℤ)) := by positivity
          omega
        _ = (n : ℤ) := by simp
    omega
  rw [Fintype.card_eq_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_succ (t n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
  binomialTMotzkinCount t (n + 1) h
    = ∑ s : binomialTMotzkinStep t, binomialTMotzkinCount t n
      (h - binomialTMotzkinHeight t s) := by
  unfold binomialTMotzkinCount
  calc Fintype.card {p : Fin (n + 1) → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1 + 1),
      0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
    ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h}
    = Fintype.card (Σ s : binomialTMotzkinStep t, {q : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s}) :=
      Fintype.card_congr ((baseEquiv t n h hh).trans (repackEquiv t n h))
    _ = ∑ s : binomialTMotzkinStep t, Fintype.card {q : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s} :=
      Fintype.card_sigma
    _ = ∑ s : binomialTMotzkinStep t, binomialTMotzkinCount t n (h - binomialTMotzkinHeight t s) :=
      Fintype.sum_congr _ _ (fun s => rfl)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinStep_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinStep_sum (t : ℕ) (f : ℤ → ℕ) :
  ∑ s : binomialTMotzkinStep t, f (binomialTMotzkinHeight t s)
    = ∑ k ∈ Finset.range (t + 1), Nat.choose t k * f (1 - (k : ℤ)) := by
  rw [Fintype.sum_sigma]
  have hconst : ∀ (k : Fin (t + 1)) (c : Fin (Nat.choose t ↑k)),
    f (binomialTMotzkinHeight t ⟨k, c⟩) = f (1 - ((↑k : ℕ) : ℤ)) := by
    intro k c
    congr 1
  have hinner : ∀ k : Fin (t + 1),
    (∑ c : Fin (Nat.choose t ↑k), f (binomialTMotzkinHeight t ⟨k, c⟩))
      = Nat.choose t ↑k * f (1 - ((↑k : ℕ) : ℤ)) := by
    intro k
    trans ∑ _c : Fin (Nat.choose t ↑k), f (1 - ((↑k : ℕ) : ℤ))
    · exact Finset.sum_congr rfl (fun c _ => hconst k c)
    · simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  trans ∑ k : Fin (t + 1), Nat.choose t ↑k * f (1 - ((↑k : ℕ) : ℤ))
  · exact Fintype.sum_congr _ _ (fun k => hinner k)
  · exact Fin.sum_univ_eq_sum_range (fun n : ℕ => Nat.choose t n * f (1 - (n : ℤ))) (t + 1)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinDeficitPoly_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinDeficitPoly_succ (t N : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N) :
  binomialTMotzkinDeficitPoly t (N + 1)
    = (1 + Polynomial.X) ^ t * binomialTMotzkinDeficitPoly t N := by
  unfold binomialTMotzkinDeficitPoly
  have hpos : 1 ≤ t * N := by
    calc 1 = 1 * 1 := by ring
    _ ≤ t * N := Nat.mul_le_mul ht hN
  have h1 : t * (N + 1) = t * N + t := by ring
  have h2 : t * (N + 1) - 1 = t + (t * N - 1) := by omega
  rw [h2, h1, pow_add]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinDeficitPoly_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinDeficitPoly_coeff_zero (t N : ℕ) :
  (binomialTMotzkinDeficitPoly t N).coeff 0 = 1 := by
  unfold binomialTMotzkinDeficitPoly
  rw [Polynomial.coeff_sub]
  have hX : (Polynomial.C (t : ℚ) * Polynomial.X * (1 + Polynomial.X) ^ (t * N - 1)).coeff 0 =
    0 := by
    rw [mul_assoc, Polynomial.coeff_C_mul]
    simp
  rw [hX, sub_zero]
  rw [Polynomial.coeff_one_add_X_pow]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinDeficitPoly_coeff_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinDeficitPoly_coeff_succ (t N r : ℕ) :
  (binomialTMotzkinDeficitPoly t N).coeff (r + 1)
    = (Nat.choose (t * N) (r + 1) : ℚ) - (t : ℚ) * (Nat.choose (t * N - 1) r : ℚ) := by
  unfold binomialTMotzkinDeficitPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow]
  congr 1
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_one_add_X_pow]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[powerSeries_coeff_mul_congr_of_coeff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma powerSeries_coeff_mul_congr_of_coeff_eq {R : Type*} [CommSemiring R]
  (U V W : PowerSeries R) (N : ℕ) (h : ∀ m ≤ N, U.coeff m = V.coeff m) :
  (W * U).coeff N = (W * V).coeff N := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hj : p.2 ≤ N := by omega
  rw [h p.2 hj]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkin_pow_coeff_shift_a](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkin_pow_coeff_shift_a (Q : PowerSeries ℚ) (t n : ℕ) :
  ((1 + PowerSeries.X * Q) ^ t).coeff (n + 1)
    = ∑ k ∈ Finset.range t, (Nat.choose t (k + 1) : ℚ) * (PowerSeries.X ^ k * Q ^ (k + 1)).coeff
      n := by
  have hcomm : (1 + PowerSeries.X * Q : PowerSeries ℚ) = PowerSeries.X * Q + 1 := by ring
  rw [hcomm, add_pow, map_sum, Finset.sum_range_succ']
  have hzero : ((PowerSeries.X * Q) ^ 0 * 1 ^ (t - 0) * Nat.cast (Nat.choose t 0)).coeff (n + 1) =
    0 := by
    simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have heq : (PowerSeries.X * Q : PowerSeries ℚ) ^ (k + 1) * 1 ^ (t - (k + 1)) * Nat.cast
    (Nat.choose t (k + 1))
    = Nat.cast (Nat.choose t (k + 1)) * (PowerSeries.X * (PowerSeries.X ^ k * Q ^ (k + 1))) := by
    ring
  rw [heq, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_succ_X_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkin_pow_coeff_shift_b](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkin_pow_coeff_shift_b (Q : PowerSeries ℚ) (t n h : ℕ) (hh : 1 ≤ h) :
  (PowerSeries.X ^ h * Q ^ h * (1 + PowerSeries.X * Q) ^ t).coeff (n + 1)
    = ∑ k ∈ Finset.range (t + 1), (Nat.choose t k : ℚ) *
      (PowerSeries.X ^ (h - 1 + k) * Q ^ (h + k)).coeff n := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hcomm : (1 + PowerSeries.X * Q : PowerSeries ℚ) = PowerSeries.X * Q + 1 := by ring
  rw [hcomm, add_pow, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have heq : (PowerSeries.X : PowerSeries ℚ) ^ (h' + 1) * Q ^ (h' + 1) *
    ((PowerSeries.X * Q) ^ k * 1 ^ (t - k) * Nat.cast (Nat.choose t k))
    = Nat.cast (Nat.choose t k) * (PowerSeries.X *
      (PowerSeries.X ^ (h' + k) * Q ^ (h' + 1 + k))) := by
    ring
  rw [heq, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_succ_X_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_succ_height](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_succ_height (t n h : ℕ) :
  binomialTMotzkinCount t (n + 1) h
    = ∑ k ∈ Finset.range (t + 1),
      Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) + (k : ℤ) - 1) := by
  calc binomialTMotzkinCount t (n + 1) h
    = ∑ s : binomialTMotzkinStep t,
      binomialTMotzkinCount t n ((h : ℤ) - binomialTMotzkinHeight t s) :=
      binomialTMotzkinCount_succ t n _ (Nat.cast_nonneg _)
    _ = ∑ k ∈ Finset.range (t + 1),
      Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) - (1 - (k : ℤ))) :=
      binomialTMotzkinStep_sum t (fun x : ℤ => binomialTMotzkinCount t n ((h : ℤ) - x))
    _ = ∑ k ∈ Finset.range (t + 1),
      Nat.choose t k * binomialTMotzkinCount t n ((h : ℤ) + (k : ℤ) - 1) := by
      apply Finset.sum_congr rfl
      intro k _
      have hkk : (h : ℤ) - (1 - (k : ℤ)) = (h : ℤ) + (k : ℤ) - 1 := by ring
      rw [hkk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_succ_zero (t n : ℕ) :
  binomialTMotzkinCount t (n + 1) 0
    = ∑ k ∈ Finset.range t,
      Nat.choose t (k + 1) * binomialTMotzkinCount t n k := by
  have hLHS : binomialTMotzkinCount t (n + 1) (0 : ℤ)
    = binomialTMotzkinCount t (n + 1) (((0 : ℕ)) : ℤ) := by simp
  have hmain := binomialTMotzkinCount_succ_height t n 0
  rw [hLHS, hmain, Finset.sum_range_succ']
  have hz : binomialTMotzkinCount t n ((((0 : ℕ)) : ℤ) + ((((0 : ℕ))) : ℤ) - 1) = 0 := by
    have hneg : (((((0 : ℕ))) : ℤ) + ((((0 : ℕ))) : ℤ) - 1 : ℤ) = -1 := by simp
    rw [hneg]
    exact binomialTMotzkinCount_of_neg t n (-1) (by norm_num)
  rw [hz, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hkk : ((((0 : ℕ)) : ℤ) + (((k + 1 : ℕ)) : ℤ) - 1) = (((k : ℕ)) : ℤ) := by push_cast; ring
  rw [hkk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_succ_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_succ_deficit (t n r : ℕ) (hr : r ≤ n + 1) :
  binomialTMotzkinCount t (n + 1) ((((n + 1 : ℕ)) : ℤ) - (((r : ℕ)) : ℤ))
    = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
      Nat.choose t ij.1 * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - (((ij.2 : ℕ)) : ℤ)) := by
  have hnat : ((((n + 1 : ℕ))) : ℤ) - ((((r : ℕ))) : ℤ) = ((((n + 1 - r : ℕ))) : ℤ) := by
    rw [← Int.natCast_sub hr]
  rw [hnat, binomialTMotzkinCount_succ_height t n (n + 1 - r),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  set m := Nat.min (t + 1) (r + 1) with hm
  have hm1 : m ≤ t + 1 := by rw [hm]; exact Nat.min_le_left _ _
  have hm2 : m ≤ r + 1 := by rw [hm]; exact Nat.min_le_right _ _
  have hF : ∀ k : ℕ, r < k →
    Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) =
      0 := by
    intro k hk
    have hgt : ((((n : ℕ))) : ℤ) < ((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1 := by omega
    rw [binomialTMotzkinCount_of_gt t n _ hgt, mul_zero]
  have hCF : ∀ k : ℕ, t < k →
    Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) =
      0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
  have hCG : ∀ k : ℕ, t < k →
    Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) = 0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
  have hL : (∑ k ∈ Finset.range (t + 1),
    Nat.choose t k * binomialTMotzkinCount t n
      (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1))
    = ∑ k ∈ Finset.range m,
      Nat.choose t k * binomialTMotzkinCount t n
        (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1) := by
    symm
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro k hk hkn
    have hkm : k < t + 1 := Finset.mem_range.mp hk
    have hnm : m ≤ k := by
      by_contra hc
      push Not at hc
      exact hkn (Finset.mem_range.mpr hc)
    have hrk : r < k := by
      by_contra hc
      push Not at hc
      have hlt : k < m := by
        rw [hm]
        exact lt_min_iff.mpr ⟨hkm, by omega⟩
      omega
    exact hF k hrk
  have hR : (∑ k ∈ Finset.range m,
    Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)))
    = ∑ k ∈ Finset.range (r + 1),
      Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by
    apply Finset.sum_subset
      (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega)))
    intro k hk hkn
    have hkm : k < r + 1 := Finset.mem_range.mp hk
    have hnm : m ≤ k := by
      by_contra hc
      push Not at hc
      exact hkn (Finset.mem_range.mpr hc)
    have htk : t < k := by
      by_contra hc
      push Not at hc
      have hlt : k < m := by
        rw [hm]
        exact lt_min_iff.mpr ⟨by omega, hkm⟩
      omega
    exact hCG k htk
  rw [hL]
  calc ∑ k ∈ Finset.range m,
    Nat.choose t k * binomialTMotzkinCount t n (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1)
    = ∑ k ∈ Finset.range m,
      Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkr : k ≤ r := by
        have hlt := Finset.mem_range.mp hk
        omega
      have he : (((((n + 1 - r : ℕ))) : ℤ) + (((k : ℕ)) : ℤ) - 1)
        = ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := by omega
      rw [he]
    _ = ∑ k ∈ Finset.range (r + 1),
      Nat.choose t k * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r - k : ℕ))) : ℤ)) := hR

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinDeficitPoly_coeff_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinDeficitPoly_coeff_top (t N : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N) :
  (binomialTMotzkinDeficitPoly t N).coeff N = 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [binomialTMotzkinDeficitPoly_coeff_succ]
  have hT : 1 ≤ t * (N' + 1) := by
    calc 1 = 1 * 1 := by ring
    _ ≤ t * (N' + 1) := Nat.mul_le_mul ht (Nat.succ_le_succ (Nat.zero_le _))
  have key := Nat.add_one_mul_choose_eq (t * (N' + 1) - 1) N'
  rw [Nat.sub_add_cancel hT] at key
  have hN' : ((((N' + 1 : ℕ))) : ℚ) ≠ 0 := by exact_mod_cast (show N' + 1 ≠ 0 by omega)
  have keyQ : ((((t * (N' + 1) : ℕ))) : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ)
    = ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by
    have hcon := congrArg (Nat.cast : ℕ → ℚ) key
    simpa [Nat.cast_mul] using hcon
  have hTeq : ((((t * (N' + 1) : ℕ))) : ℚ) = (t : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by push_cast; ring
  rw [hTeq] at keyQ
  have hC : ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ)
    = (t : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ) := by
    have keyQ2 : ((t : ℚ) * ((((Nat.choose (t * (N' + 1) - 1) N' : ℕ))) : ℚ)) *
      ((((N' + 1 : ℕ))) : ℚ)
      = ((((Nat.choose (t * (N' + 1)) (N' + 1) : ℕ))) : ℚ) * ((((N' + 1 : ℕ))) : ℚ) := by
      linear_combination keyQ
    exact (mul_right_cancel₀ hN' keyQ2).symm
  rw [hC]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinDeficitPoly_coeff_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinDeficitPoly_coeff_pred (t n : ℕ) (ht : 1 ≤ t) :
  (binomialTMotzkinDeficitPoly t (n + 1)).coeff n
    = ((((Nat.choose (t * (n + 1)) (n + 1) : ℕ))) : ℚ)
      / (((((t - 1) * (n + 1) + 1 : ℕ))) : ℚ) := by
  cases n with
  | zero =>
    rw [binomialTMotzkinDeficitPoly_coeff_zero]
    have e0 : (0 + 1 : ℕ) = 1 := rfl
    rw [e0, Nat.mul_one, Nat.choose_one_right, Nat.mul_one]
    have eT : t - 1 + 1 = t := Nat.sub_add_cancel ht
    rw [eT]
    have htoc : ((t : ℚ)) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    rw [div_self htoc]
  | succ m =>
    rw [binomialTMotzkinDeficitPoly_coeff_succ]
    have hT : 1 ≤ t * ((m + 1) + 1) := by
      calc 1 = 1 * 1 := by ring
      _ ≤ t * ((m + 1) + 1) := Nat.mul_le_mul ht (by omega)
    have abs1 := Nat.add_one_mul_choose_eq (t * ((m + 1) + 1) - 1) m
    rw [Nat.sub_add_cancel hT] at abs1
    have abs2 := Nat.choose_succ_right_eq (t * ((m + 1) + 1)) (m + 1)
    have hTD : t * ((m + 1) + 1) - (m + 1) = (t - 1) * ((m + 1) + 1) + 1 := by
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have hexpand : (t' + 1) * ((m + 1) + 1) = t' * ((m + 1) + 1) + ((m + 1) + 1) := by ring
      rw [hexpand, Nat.add_sub_assoc (by omega : m + 1 ≤ (m + 1) + 1)]
      have hM : ((m + 1) + 1) - (m + 1) = 1 := by omega
      rw [hM]
    have abs1c : ((((t * ((m + 1) + 1) : ℕ))) : ℚ) *
      ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
      = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) abs1
      simpa [Nat.cast_mul] using hcon
    have abs2c : ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
      * (((((m + 1) + 1 : ℕ))) : ℚ)
      = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
        * ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) abs2
      simpa [Nat.cast_mul] using hcon
    have hTDc : ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ)
      = (((( (t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by
      have hcon := congrArg (Nat.cast : ℕ → ℚ) hTD
      simpa [Nat.cast_mul, Nat.cast_add] using hcon
    have hTc : ((((t * ((m + 1) + 1) : ℕ))) : ℚ)
      = (t : ℚ) * (((((m + 1) + 1 : ℕ))) : ℚ) := by push_cast; ring
    have hDpos : (0 : ℚ) < (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) :=
      Nat.cast_pos.mpr (by omega)
    have hEpos : (0 : ℚ) < (((((m + 1) + 1 : ℕ))) : ℚ) := Nat.cast_pos.mpr (by omega)
    have hDn : (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) ≠ 0 := ne_of_gt hDpos
    have hEn : (((((m + 1) + 1 : ℕ))) : ℚ) ≠ 0 := ne_of_gt hEpos
    have step1 : ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ)
      = (t : ℚ) * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
        * (((((m + 1) + 1 : ℕ))) : ℚ) := by
      calc ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ) * ((((m + 1 : ℕ))) : ℚ)
        = ((((t * ((m + 1) + 1) : ℕ))) : ℚ)
          * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ) := abs1c.symm
        _ = (t : ℚ) * (((((m + 1) + 1 : ℕ))) : ℚ)
          * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ) := by rw [hTc]
        _ = (t : ℚ) * ((((Nat.choose (t * ((m + 1) + 1) - 1) m : ℕ))) : ℚ)
          * (((((m + 1) + 1 : ℕ))) : ℚ) := by ring
    have step2 : ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
      * (((((m + 1) + 1 : ℕ))) : ℚ)
      = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
        * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by
      calc ((((Nat.choose (t * ((m + 1) + 1)) ((m + 1) + 1) : ℕ))) : ℚ)
        * (((((m + 1) + 1 : ℕ))) : ℚ)
        = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
          * ((((t * ((m + 1) + 1) - (m + 1) : ℕ))) : ℚ) := abs2c
        _ = ((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
          * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) := by rw [hTDc]
    have hE1v : (((((m + 1) + 1 : ℕ))) : ℚ) - ((((m + 1 : ℕ))) : ℚ) - 1 = 0 := by
      push_cast; ring
    rw [eq_div_iff hDn]
    apply mul_right_cancel₀ hEn
    linear_combination
      (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ) * step1
      - step2
      + (((((Nat.choose (t * ((m + 1) + 1)) (m + 1) : ℕ))) : ℚ)
        * (((((t - 1) * ((m + 1) + 1) + 1 : ℕ))) : ℚ)) * hE1v

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinCount_eq_deficitPoly_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinCount_eq_deficitPoly_coeff (t n : ℕ) (ht : 1 ≤ t) :
  ∀ r : ℕ, r ≤ n + 1 →
    ((((binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((r : ℕ))) : ℤ)) : ℕ))) : ℚ)
    = (binomialTMotzkinDeficitPoly t (n + 1)).coeff r := by
  induction n with
  | zero =>
    intro r hr
    interval_cases r
    · have h00 : ((((0 : ℕ))) : ℤ) - ((((0 : ℕ))) : ℤ) = 0 := by simp
      have eG : (0 + 1 : ℕ) = 1 := rfl
      rw [h00, binomialTMotzkinCount_zero]
      simp only [ite_true, Nat.cast_one]
      rw [eG]
      exact (binomialTMotzkinDeficitPoly_coeff_zero t 1).symm
    · have h01 : ((((0 : ℕ))) : ℤ) - ((((1 : ℕ))) : ℤ) = -1 := by simp
      have eG : (0 + 1 : ℕ) = 1 := rfl
      rw [h01, binomialTMotzkinCount_of_neg t 0 (-1) (by norm_num)]
      simp only [Nat.cast_zero]
      rw [eG]
      exact (binomialTMotzkinDeficitPoly_coeff_top t 1 ht (by omega)).symm
  | succ n ih =>
    intro r hr
    by_cases hr' : r ≤ n + 1
    · rw [binomialTMotzkinCount_succ_deficit t n r hr', Nat.cast_sum]
      have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        ((((Nat.choose t ij.1
          * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((ij.2 : ℕ))) : ℤ)) : ℕ))) : ℚ)
        = ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff
          ij.2 := by
        intro ij hij
        have hj : ij.2 ≤ n + 1 := by
          have hmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          omega
        have hih := ih ij.2 hj
        rw [Nat.cast_mul, hih]
      have hsum : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        ((((Nat.choose t ij.1
          * binomialTMotzkinCount t n ((((n : ℕ)) : ℤ) - ((((ij.2 : ℕ))) : ℤ)) : ℕ))) : ℚ))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
          ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff
            ij.2 :=
        Finset.sum_congr rfl (fun ij hij => hterm ij hij)
      rw [hsum]
      have hmul : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
        ((((Nat.choose t ij.1 : ℕ))) : ℚ) * (binomialTMotzkinDeficitPoly t (n + 1)).coeff ij.2)
        = (((1 + Polynomial.X) ^ t * binomialTMotzkinDeficitPoly t (n + 1))).coeff r := by
        rw [Polynomial.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij _
        rw [Polynomial.coeff_one_add_X_pow]
      rw [hmul]
      have hG := binomialTMotzkinDeficitPoly_succ t (n + 1) ht (by omega : 1 ≤ n + 1)
      rw [hG]
    · have hrEq : r = n + 2 := by omega
      subst hrEq
      have hneg : ((((n + 1 : ℕ))) : ℤ) - ((((n + 2 : ℕ))) : ℤ) = -1 := by push_cast; ring
      rw [hneg, binomialTMotzkinCount_of_neg t (n + 1) _ (by norm_num : (-1 : ℤ) < 0),
        Nat.cast_zero]
      have htop := binomialTMotzkinDeficitPoly_coeff_top t (n + 2) ht (by omega)
      exact htop.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkinPS_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkinPS_coeff (t n : ℕ) :
  (binomialTMotzkinPS t).coeff n = ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ) := by
  unfold binomialTMotzkinPS
  rw [PowerSeries.coeff_mk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkin_catalanGF_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkin_catalanGF_eq (t : ℕ) (ht : 1 ≤ t) :
  PowerSeries.mk (fun n => ((((Nat.choose (t * n) n : ℕ))) : ℚ) / (((((t - 1) * n + 1 : ℕ))) : ℚ))
    = 1 + PowerSeries.X * binomialTMotzkinPS t := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    have e1 : t * 0 = 0 := Nat.mul_zero t
    have e2 : (t - 1) * 0 + 1 = 1 := by omega
    simp only [PowerSeries.coeff_mk, e1, e2, Nat.choose_zero_right, Nat.cast_one, div_one]
    simp [map_add]
  | succ n =>
    rw [PowerSeries.coeff_mk]
    have hR : ((1 + PowerSeries.X * binomialTMotzkinPS t : PowerSeries ℚ)).coeff (n + 1)
      = ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ) := by
      rw [map_add]
      have h1 : ((1 : PowerSeries ℚ)).coeff (n + 1) = 0 := by simp
      rw [h1, zero_add, PowerSeries.coeff_succ_X_mul, binomialTMotzkinPS_coeff]
    rw [hR]
    have hN8 := binomialTMotzkinCount_eq_deficitPoly_coeff t n ht n (by omega : n ≤ n + 1)
    have hN7 := binomialTMotzkinDeficitPoly_coeff_pred t n ht
    have h00 : ((((n : ℕ))) : ℤ) - ((((n : ℕ))) : ℤ) = 0 := by simp
    rw [h00] at hN8
    rw [hN8, hN7]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomialTMotzkin_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
private lemma binomialTMotzkin_fixedPoint (t : ℕ) :
  binomialTMotzkinPS t = (1 + PowerSeries.X * binomialTMotzkinPS t) ^ t := by
  have key : ∀ n : ℕ,
    (∀ m, m ≤ n → (binomialTMotzkinPS t).coeff m
      = ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff m)
    ∧ (∀ h : ℕ, ((((binomialTMotzkinCount t n ((((h : ℕ))) : ℤ) : ℕ))) : ℚ)
      = (PowerSeries.X ^ h * binomialTMotzkinPS t ^ (h + 1)).coeff n) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        have hL : (binomialTMotzkinPS t).coeff 0 = 1 := by
          rw [binomialTMotzkinPS_coeff, binomialTMotzkinCount_zero]
          simp
        have hR : ((1 + PowerSeries.X * binomialTMotzkinPS t : PowerSeries ℚ) ^ t).coeff 0
          = 1 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_add,
            PowerSeries.constantCoeff_one, map_mul, PowerSeries.constantCoeff_X, zero_mul,
            add_zero, one_pow]
        rw [hL, hR]
      · intro h
        cases h with
        | zero =>
          simp only [pow_zero, one_mul, Nat.zero_add, pow_one, binomialTMotzkinPS_coeff,
            Nat.cast_zero]
        | succ m =>
          have hne : ((((m + 1 : ℕ))) : ℤ) ≠ 0 := by
            exact_mod_cast (by omega : m + 1 ≠ 0)
          have hL : binomialTMotzkinCount t 0 (((m + 1 : ℕ)) : ℤ) = 0 := by
            rw [binomialTMotzkinCount_zero, ite_eq_right hne]
          rw [hL, Nat.cast_zero, PowerSeries.coeff_X_pow_mul']
          simp
    | succ n ih =>
      obtain ⟨ihC, ihD⟩ := ih
      have ihC' : ∀ m, m ≤ n + 1 → (binomialTMotzkinPS t).coeff m
        = ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff m := by
        intro m hm
        by_cases hm' : m ≤ n
        · exact ihC m hm'
        · have hmn : m = n + 1 := by omega
          subst hmn
          have hP : (binomialTMotzkinPS t).coeff (n + 1)
            = ∑ k ∈ Finset.range t, ((((Nat.choose t (k + 1) : ℕ))) : ℚ)
              * (PowerSeries.X ^ k * binomialTMotzkinPS t ^ (k + 1)).coeff n := by
            rw [binomialTMotzkinPS_coeff, binomialTMotzkinCount_succ_zero, Nat.cast_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [Nat.cast_mul, ihD k]
          have hshiftA := binomialTMotzkin_pow_coeff_shift_a (binomialTMotzkinPS t) t n
          rw [hP, hshiftA]
      have ihD' : ∀ h : ℕ, ((((binomialTMotzkinCount t (n + 1) ((((h : ℕ))) : ℤ) : ℕ))) : ℚ)
        = (PowerSeries.X ^ h * binomialTMotzkinPS t ^ (h + 1)).coeff (n + 1) := by
        intro h
        cases h with
        | zero =>
          simp only [pow_zero, one_mul, Nat.zero_add, pow_one, binomialTMotzkinPS_coeff,
            Nat.cast_zero]
        | succ m =>
          have hadd : ∀ k : ℕ, m + 1 + k = m + k + 1 := fun k => by ring
          have hshift := binomialTMotzkin_pow_coeff_shift_b (binomialTMotzkinPS t) t n (m + 1)
            (by omega)
          simp only [Nat.add_sub_cancel, hadd] at hshift
          have hcount : ((((binomialTMotzkinCount t (n + 1) (((((m + 1) : ℕ))) : ℤ) : ℕ))) : ℚ)
            = (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1)
              * (1 + PowerSeries.X * binomialTMotzkinPS t) ^ t).coeff (n + 1) := by
            rw [binomialTMotzkinCount_succ_height t n (m + 1), Nat.cast_sum, hshift]
            apply Finset.sum_congr rfl
            intro k _
            have hk : ((((m + 1 : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ) - 1
              = ((((m + k : ℕ))) : ℤ) := by omega
            rw [Nat.cast_mul, hk, ihD (m + k)]
          have hN10 := powerSeries_coeff_mul_congr_of_coeff_eq
            ((1 + PowerSeries.X * binomialTMotzkinPS t) ^ t)
            (binomialTMotzkinPS t)
            (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1))
            (n + 1) (fun m hm => (ihC' m hm).symm)
          have hps : binomialTMotzkinPS t ^ (m + 1 + 1)
            = binomialTMotzkinPS t ^ (m + 1) * binomialTMotzkinPS t := pow_succ _ _
          have hRHS : (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1)
            * binomialTMotzkinPS t).coeff (n + 1)
            = (PowerSeries.X ^ (m + 1) * binomialTMotzkinPS t ^ (m + 1 + 1)).coeff
              (n + 1) := by
            rw [hps, mul_assoc]
          rw [hcount, hN10, hRHS]
      exact ⟨ihC', ihD'⟩
  apply PowerSeries.ext
  intro n
  exact (key n).1 n le_rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomial_tMotzkin_generatingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean)
-/
@[path]
lemma binomial_tMotzkin_generatingFunction
  {t : ℕ}
-- given
  (ht : 1 ≤ t) :
-- imply
  let Step := by
-- proof
  intro Step heightChange pathCount catalanGF
  have hPS : PowerSeries.mk (fun n => (((pathCount n : ℕ)) : ℚ))
    = binomialTMotzkinPS t := rfl
  have hCG : catalanGF
    = PowerSeries.mk (fun n => ((((Nat.choose (t * n) n : ℕ))) : ℚ)
      / (((((t - 1) * n + 1 : ℕ))) : ℚ)) := rfl
  rw [hPS, hCG, binomialTMotzkin_catalanGF_eq t ht]
  exact binomialTMotzkin_fixedPoint t
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-23
