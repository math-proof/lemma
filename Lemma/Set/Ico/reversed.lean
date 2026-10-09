import sympy.sets.fancysets
import sympy.Basic


@[path]
private lemma main
  {a b k : ℤ}
-- given
  (hk : k ≠ 0) :
-- imply
  Range a b k = (Range (a + (((b - a) * k.sign + |k| - 1) / |k| - 1) * k) (a - k.sign) (-k)).reverse := by
-- proof
  set s : ℤ := k.sign with hs
  set abs_k : ℤ := |k| with habs
  have habs_pos : 0 < abs_k := by
    rw [habs]
    exact abs_pos.mpr hk
  have habs_ne : abs_k ≠ 0 := habs_pos.ne'
  set n : ℤ := ((b - a) * s + abs_k - 1) / abs_k with hn
  have hsk : s * k = abs_k := by
    rw [hs, habs]
    exact?
  have hs2 : s ^ 2 = 1 := by
    rw [hs]
    if h : 0 < k then
      rw [Int.sign_eq_one_of_pos h]
      norm_num
    else
      have h' : k < 0 := by omega
      rw [Int.sign_eq_neg_one_of_neg h']
      norm_num
  have hns : (-k).sign = -s := by
    rw [hs]
    simp [Int.sign_neg]
  have habs_neg : |-k| = abs_k := by
    rw [habs]
    simp
  have hdiv_eq : ((b - a) * k.sign + |k| - 1) / |k| = n := by
    simpa [hs, habs] using hn.symm
  have hlen : (((a - s) - (a + (n - 1) * k)) * (-k).sign + |-k| - 1) / |-k| = n := by
    rw [hns, habs_neg]
    have h : ((a - s) - (a + (n - 1) * k)) * (-s) + abs_k - 1 = abs_k * n := calc
      _ = (a - s - a - k * (n - 1)) * (-s) + abs_k - 1 := by ring
      _ = (-s - k * (n - 1)) * (-s) + abs_k - 1 := by ring
      _ = s ^ 2 + s * k * (n - 1) + abs_k - 1 := by ring
      _ = 1 + abs_k * (n - 1) + abs_k - 1 := by rw [hs2, hsk]
      _ = abs_k * n := by ring
    rw [h]
    rw [Int.mul_ediv_cancel_left _ habs_ne]
  have hnorm : Range a b k = (List.range n.toNat).map (fun i : ℕ => a + (i : ℤ) * k) := by
    unfold Range
    rw [hdiv_eq]
    show List.map (fun x : ℤ => a + x * k) (List.flatMap (fun j : ℕ => [(j : ℤ)]) (List.range n.toNat)) = _
    rw [← List.map_eq_flatMap, List.map_map]
    rfl
  have hnorm2 : Range (a + (n - 1) * k) (a - s) (-k) = (List.range n.toNat).map (fun i : ℕ => (a + (n - 1) * k) + (i : ℤ) * (-k)) := by
    unfold Range
    rw [hlen]
    show List.map (fun x : ℤ => (a + (n - 1) * k) + x * (-k)) (List.flatMap (fun j : ℕ => [(j : ℤ)]) (List.range n.toNat)) = _
    rw [← List.map_eq_flatMap, List.map_map]
    rfl
  have hmain : Range a b k = (Range (a + (n - 1) * k) (a - s) (-k)).reverse := by
    rw [hnorm, hnorm2]
    rw [← List.map_reverse]
    apply List.ext_getElem
    · simp
    ·
      intro i hi h₂
      have hi' : i < n.toNat := by simpa using hi
      have hn_pos : 0 < n := by
        by_contra h
        have h' : n ≤ 0 := by omega
        have hz : n.toNat = 0 := Int.toNat_of_nonpos h'
        rw [hz] at hi'
        exact Nat.not_lt_zero i hi'
      have h_nonneg : 0 ≤ n := by linarith
      have h_toNat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h_nonneg
      have h1n : 1 ≤ n.toNat := by
        refine (Nat.cast_le (α := ℤ)).mp ?_
        rwa [h_toNat]
      have hle : i ≤ n.toNat - 1 := by
        rw [Nat.le_sub_iff_add_le h1n]
        exact Nat.lt_iff_add_one_le.mp hi'
      have hcast : ((n.toNat - 1 - i : ℕ) : ℤ) = n - 1 - (i : ℤ) := by
        rw [Nat.cast_sub hle, Nat.cast_sub h1n, Nat.cast_one, h_toNat]
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, hcast]
      ring
  simpa [hs] using hmain


-- created on 2026-10-07
