import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MeromorphicStirlingNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[meromorphicStirlingFirst_eq_besselNumberFirst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean)
-/
@[path]
lemma meromorphicStirlingFirst_eq_besselNumberFirst
  {n k : ℕ}
-- given
  (h0 : 1 ≤ k)
  (h1 : k ≤ n) :
-- imply
  meromorphicStirlingFirst n k = besselNumberFirst n k := by
-- proof
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h2
  have hnm : 1 + k' + m = (k' + m) + 1 := by ring
  have e_n1 : 1 + k' + m - 1 = k' + m := by rw [hnm, Nat.add_sub_cancel]
  have hkk : 1 + k' = k' + 1 := by ring
  have e_k1 : 1 + k' - 1 = k' := by rw [hkk, Nat.add_sub_cancel]
  have hnk : 1 + k' + m = (1 + k') + m := by ring
  have e_nk : 1 + k' + m - (1 + k') = m := by rw [hnk, Nat.add_sub_cancel_left]
  have h2n : 2 * (1 + k' + m) = (1 + k') + ((k' + 2 * m) + 1) := by ring
  have estep : 2 * (1 + k' + m) - (1 + k') = (k' + 2 * m) + 1 := by
    rw [h2n, Nat.add_sub_cancel_left]
  have e_N : 2 * (1 + k' + m) - (1 + k') - 1 = k' + 2 * m := by
    rw [estep, Nat.add_sub_cancel]
  have hmm : k' + 2 * m = (k' + m) + m := by ring
  have hle_add : k' + m ≤ k' + 2 * m := by
    rw [hmm]
    exact Nat.le_add_right _ _
  have hle : 1 + k' + m - 1 ≤ 2 * (1 + k' + m) - (1 + k') - 1 := by
    rwa [e_n1, e_N]
  have hsub_add : k' + 2 * m - (k' + m) = m := by
    rw [hmm, Nat.add_sub_cancel_left]
  have hsub : 2 * (1 + k' + m) - (1 + k') - 1 - (1 + k' + m - 1) =
    1 + k' + m - (1 + k') := by
    rwa [e_N, e_n1, e_nk]
  have hChoose := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hChoose
  have hcast := congrArg (fun x : ℕ => (x : ℚ)) hChoose
  simp only [Nat.cast_mul] at hcast
  have key : (((1 + k' + m - 1).factorial : ℕ) : ℚ) *
    ((Nat.choose (2 * (1 + k' + m) - (1 + k') - 1) (1 + k' + m - 1) : ℕ) : ℚ) *
    ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ) =
    ((((2 * (1 + k' + m) - (1 + k') - 1).factorial : ℕ)) : ℚ) := by
    linear_combination hcast
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hv : (2 : ℚ) ^ (1 + k' + m - (1 + k')) ≠ 0 := pow_ne_zero _ h2ne
  have hw : ((((1 + k') - 1).factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : (2 : ℚ) ^ (1 + k' + m - (1 + k')) *
    ((((1 + k') - 1).factorial : ℕ) : ℚ) ≠ 0 :=
    mul_ne_zero hv hw
  have eS : meromorphicStirlingFirst (1 + k' + m) (1 + k') =
    ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k' + m - 1).factorial : ℕ)) : ℚ) *
      ((Nat.choose (2 * (1 + k' + m) - (1 + k') - 1) (1 + k' + m - 1) : ℕ) : ℚ)) /
    ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k') - 1).factorial : ℕ) : ℚ)) := by
    unfold meromorphicStirlingFirst
    ring
  have eB : besselNumberFirst (1 + k' + m) (1 + k') =
    ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((2 * (1 + k' + m) - (1 + k') - 1).factorial : ℕ)) : ℚ)) /
    ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k') - 1).factorial : ℕ) : ℚ) *
      ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ)) := by
    unfold besselNumberFirst
    ring
  rw [eS, eB, div_eq_div_iff hd (mul_ne_zero hd hF3)]
  linear_combination ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
    ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k') - 1).factorial : ℕ) : ℚ))) * key

end MetaMathlibExt

namespace MetaMathlibExt

/--
[meromorphicStirlingSecond_eq_besselNumberSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean)
-/
@[path]
lemma meromorphicStirlingSecond_eq_besselNumberSecond
  {n k : ℕ}
-- given
  (h0 : n ≤ 2 * k)
  (h1 : k ≤ n) :
-- imply
  meromorphicStirlingSecond n k = besselNumberSecond n k := by
-- proof
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le h1
  have hkk : k + k = 2 * k := by ring
  have hass : (k + t) + u = k + (t + u) := by ring
  have htu : k + k = k + (t + u) := by rw [hkk, hu, hass]
  have hks : k = t + u := by omega
  subst hks
  have e_2kn : 2 * (t + u) - ((t + u) + t) = u := by
    rw [hu, Nat.add_sub_cancel_left]
  have h2n : 2 * ((t + u) + t) = 2 * (t + u) + 2 * t := by ring
  have e_2n2k : 2 * ((t + u) + t) - 2 * (t + u) = 2 * t := by
    rw [h2n, Nat.add_sub_cancel_left]
  have e_nk : (t + u) + t - (t + u) = t := by omega
  have hns : (t + u) + t = 2 * t + u := by ring
  have e_nsub : (t + u) + t - u = 2 * t := by
    rw [hns, Nat.add_sub_cancel]
  have hle_add : u ≤ 2 * t + u := Nat.le_add_left _ _
  have hle' : 2 * (t + u) - ((t + u) + t) ≤ (t + u) + t := by
    rwa [e_2kn, hns]
  have hsub' : (t + u) + t - (2 * (t + u) - ((t + u) + t)) =
    2 * ((t + u) + t) - 2 * (t + u) := by
    rw [e_2kn, e_nsub, e_2n2k]
  have hChoose2 := Nat.choose_mul_factorial_mul_factorial hle'
  rw [hsub'] at hChoose2
  have hcast2 := congrArg (fun x : ℕ => (x : ℚ)) hChoose2
  simp only [Nat.cast_mul] at hcast2
  have key2 : ((((2 * ((t + u) + t) - 2 * (t + u)).factorial : ℕ)) : ℚ) *
    ((Nat.choose ((t + u) + t) (2 * (t + u) - ((t + u) + t)) : ℕ) : ℚ) *
    ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ) =
    ((((((t + u) + t).factorial : ℕ))) : ℚ) := by
    linear_combination hcast2
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hv : (2 : ℚ) ^ ((t + u) + t - (t + u)) ≠ 0 := pow_ne_zero _ h2ne
  have hFt : (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : (2 : ℚ) ^ ((t + u) + t - (t + u)) *
    (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) ≠ 0 :=
    mul_ne_zero hv hFt
  have eS2 : meromorphicStirlingSecond ((t + u) + t) (t + u) =
    (((((2 * ((t + u) + t) - 2 * (t + u)).factorial : ℕ))) : ℚ) *
      ((Nat.choose ((t + u) + t) (2 * (t + u) - ((t + u) + t)) : ℕ) : ℚ) /
    ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
      (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ)) := by
    unfold meromorphicStirlingSecond
    ring
  have eB2 : besselNumberSecond ((t + u) + t) (t + u) =
    ((((((t + u) + t).factorial : ℕ))) : ℚ) /
    ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
      (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) *
      ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ)) := by
    unfold besselNumberSecond
    ring
  rw [eS2, eB2, div_eq_div_iff hd (mul_ne_zero hd hF3)]
  linear_combination ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
    (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ)) * key2

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
