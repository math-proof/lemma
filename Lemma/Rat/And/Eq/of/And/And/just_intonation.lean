import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (l1 l2 l3 l4 l5 l6 l7 l7l l1s l2s l4s l5s l6s l1d l1ds l2d l2ds l3d : ℚ)
-- given
  (h₀ :
    l7 / l7l = l1d / l1 ∧
      l1d / l1 = l1ds / l1s ∧
      l1ds / l1s = l2d / l2 ∧
      l2d / l2 = l2ds / l2s ∧
      l2ds / l2s = l3d / l3 ∧
      l3d / l3 = (1 : ℚ) / 2)
  (h₁ :
    l4s / l7l = l5 / l1 ∧
      l5 / l1 = l5s / l1s ∧
      l5s / l1s = l6 / l2 ∧
      l6 / l2 = l6s / l2s ∧
      l6s / l2s = l7 / l3 ∧
      l7 / l3 = l1d / l4 ∧
      l1d / l4 = l1ds / l4s ∧
      l1ds / l4s = l2d / l5 ∧
      l2d / l5 = l2ds / l5s ∧
      l2ds / l5s = l3d / l6 ∧
      l3d / l6 = (2 : ℚ) / 3)
  (h₂ :
    l1 ≠ 0 ∧ l1s ≠ 0 ∧ l2 ≠ 0 ∧ l2s ≠ 0 ∧ l3 ≠ 0 ∧
      l4 ≠ 0 ∧ l4s ≠ 0 ∧ l5 ≠ 0 ∧ l5s ≠ 0 ∧ l6 ≠ 0 ∧ l7l ≠ 0) :
-- imply
  (l1s / l1 = l2s / l2 ∧ l2s / l2 = l4s / l4 ∧ l4s / l4 = l5s / l5 ∧ l5s / l5 = l6s / l6 ∧
      l6s / l6 = (2 : ℚ) ^ 11 / 3 ^ 7) ∧
    (l1 / l7l = l2 / l1s ∧ l2 / l1s = l3 / l2s ∧ l3 / l2s = l4 / l3 ∧ l4 / l3 = l5 / l4s ∧
      l5 / l4s = l6 / l5s ∧ l6 / l5s = l7 / l6s ∧ l7 / l6s = (3 : ℚ) ^ 5 / 2 ^ 8) ∧
    l2 / l1 = 8 / 9 ∧
    l4 / l1 = 3 / 4 := by
-- proof
  obtain ⟨hl1, hl1s, hl2, hl2s, hl3, hl4, hl4s, hl5, hl5s, hl6, hl7l⟩ := h₂
  obtain ⟨o7, o1d, o1ds, o2d, o2ds, o3d⟩ := h₀
  obtain ⟨f4s, f5, f5s, f6, f6s, f7, f1d, f1ds, f2d, f2ds, f3d⟩ := h₁
  have e1d : 2 * l1d = l1 := by
    have : l1d / l1 = (1 : ℚ) / 2 := o1d.trans (o1ds.trans (o2d.trans (o2ds.trans o3d)))
    field_simp [hl1] at this
    linear_combination this
  have e1ds : 2 * l1ds = l1s := by
    have : l1ds / l1s = (1 : ℚ) / 2 := o1ds.trans (o2d.trans (o2ds.trans o3d))
    field_simp [hl1s] at this
    linear_combination this
  have e2d : 2 * l2d = l2 := by
    have : l2d / l2 = (1 : ℚ) / 2 := o2d.trans (o2ds.trans o3d)
    field_simp [hl2] at this
    linear_combination this
  have e2ds : 2 * l2ds = l2s := by
    have : l2ds / l2s = (1 : ℚ) / 2 := o2ds.trans o3d
    field_simp [hl2s] at this
    linear_combination this
  have e3d : 2 * l3d = l3 := by
    field_simp [hl3] at o3d
    linear_combination o3d
  have e7 : 2 * l7 = l7l := by
    have : l7 / l7l = (1 : ℚ) / 2 := o7.trans (o1d.trans (o1ds.trans (o2d.trans (o2ds.trans o3d))))
    field_simp [hl7l] at this
    linear_combination this
  have g5 : 3 * l5 = 2 * l1 := by
    have : l5 / l1 = (2 : ℚ) / 3 :=
      f5.trans (f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))))))
    field_simp [hl1] at this
    linear_combination this
  have g5s : 3 * l5s = 2 * l1s := by
    have : l5s / l1s = (2 : ℚ) / 3 :=
      f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))))
    field_simp [hl1s] at this
    linear_combination this
  have g6 : 3 * l6 = 2 * l2 := by
    have : l6 / l2 = (2 : ℚ) / 3 :=
      f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))))
    field_simp [hl2] at this
    linear_combination this
  have g6s : 3 * l6s = 2 * l2s := by
    have : l6s / l2s = (2 : ℚ) / 3 :=
      f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))
    field_simp [hl2s] at this
    linear_combination this
  have g7 : 3 * l7 = 2 * l3 := by
    have : l7 / l3 = (2 : ℚ) / 3 := f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d))))
    field_simp [hl3] at this
    linear_combination this
  have g1d4 : 3 * l1d = 2 * l4 := by
    have : l1d / l4 = (2 : ℚ) / 3 := f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))
    field_simp [hl4] at this
    linear_combination this
  have g1ds : 3 * l1ds = 2 * l4s := by
    have : l1ds / l4s = (2 : ℚ) / 3 := f1ds.trans (f2d.trans (f2ds.trans f3d))
    field_simp [hl4s] at this
    linear_combination this
  have hl5' : l5 ≠ 0 := by
    have h : 2 * l1 ≠ 0 := mul_ne_zero (by norm_num) hl1
    rw [← g5] at h
    exact right_ne_zero_of_mul h
  have g2d5 : 3 * l2d = 2 * l5 := by
    have : l2d / l5 = (2 : ℚ) / 3 := f2d.trans (f2ds.trans f3d)
    field_simp [hl5'] at this
    linear_combination this
  have hl5s' : l5s ≠ 0 := by
    have h : 2 * l1s ≠ 0 := mul_ne_zero (by norm_num) hl1s
    rw [← g5s] at h
    exact right_ne_zero_of_mul h
  have g2ds : 3 * l2ds = 2 * l5s := by
    have : l2ds / l5s = (2 : ℚ) / 3 := f2ds.trans f3d
    field_simp [hl5s'] at this
    linear_combination this
  have hl6' : l6 ≠ 0 := by
    have h : 2 * l2 ≠ 0 := mul_ne_zero (by norm_num) hl2
    rw [← g6] at h
    exact right_ne_zero_of_mul h
  have g3d6 : 3 * l3d = 2 * l6 := by
    field_simp [hl6'] at f3d
    linear_combination f3d
  have g4s : 3 * l4s = 2 * l7l := by
    have : l4s / l7l = (2 : ℚ) / 3 :=
      f4s.trans (f5.trans (f5s.trans (f6.trans (f6s.trans (f7.trans (f1d.trans (f1ds.trans (f2d.trans (f2ds.trans f3d)))))))))
    field_simp [hl7l] at this
    linear_combination this
  have h4p : 4 * l4 = 3 * l1 := by
    linear_combination 3 * e1d - 2 * g1d4
  have h2p : 9 * l2 = 8 * l1 := by
    linear_combination -9 * e2d + 6 * g2d5 + 4 * g5
  have h21s : 9 * l2s = 8 * l1s := by
    linear_combination -9 * e2ds + 6 * g2ds + 4 * g5s
  have h32 : 9 * l3 = 8 * l2 := by
    linear_combination -9 * e3d + 6 * g3d6 + 4 * g6
  have h31 : 81 * l3 = 64 * l1 := by
    linear_combination 9 * h32 + 8 * h2p
  have h7l : 8 * l7l = 9 * l1s := by
    linear_combination -4 * g4s - 6 * g1ds + 9 * e1ds
  have h37 : 4 * l3 = 3 * l7l := by
    linear_combination 3 * e7 - 2 * g7
  have h3s : 32 * l3 = 27 * l1s := by
    linear_combination 8 * h37 + 3 * h7l
  have h4s : 4 * l4s = 3 * l1s := by
    linear_combination 3 * e1ds - 2 * g1ds
  have h63 : 4 * l6 = 3 * l3 := by
    linear_combination 3 * e3d - 2 * g3d6
  have hl6s : l6s ≠ 0 := by
    have h : 2 * l2s ≠ 0 := mul_ne_zero (by norm_num) hl2s
    rw [← g6s] at h
    exact right_ne_zero_of_mul h
  have hl7 : l7 ≠ 0 := by
    have h : l7l ≠ 0 := hl7l
    rw [← e7] at h
    exact right_ne_zero_of_mul h
  have hsharp : 2187 * l1s = 2048 * l1 := by
    linear_combination 32 * h31 - 81 * h3s
  have h17 : 243 * l7l = 256 * l1 := by
    linear_combination ((2187 / 9) * h7l + hsharp) / 8
  have h4 : l4 / l1 = 3 / 4 := by
    field_simp [hl1, hl4]
    linear_combination h4p
  have h2 : l2 / l1 = 8 / 9 := by
    field_simp [hl1, hl2]
    linear_combination h2p
  have hs : l1s / l1 = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    field_simp [hl1, hl1s]
    norm_num
    linear_combination hsharp
  have hs2 : l2s / l2 = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h2v : l2 = (8 / 9) * l1 := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : l2s = (8 / 9) * l1s := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs4 : l4s / l4 = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h4v : l4 = (3 / 4) * l1 := by
      field_simp [hl4]
      linear_combination h4p
    have h4sv : l4s = (3 / 4) * l1s := by
      field_simp [hl4s]
      linear_combination h4s
    rw [h4v, h4sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs5 : l5s / l5 = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h5v : l5 = (2 / 3) * l1 := by
      field_simp [hl5']
      linear_combination g5
    have h5sv : l5s = (2 / 3) * l1s := by
      field_simp [hl5s']
      linear_combination g5s
    rw [h5v, h5sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hs6 : l6s / l6 = (2 : ℚ) ^ 11 / 3 ^ 7 := by
    have h6v : l6 = (2 / 3) * l2 := by
      field_simp [hl6']
      linear_combination g6
    have h6sv : l6s = (2 / 3) * l2s := by
      field_simp [hl6s]
      linear_combination g6s
    have h2v : l2 = (8 / 9) * l1 := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : l2s = (8 / 9) * l1s := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h6v, h6sv, h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination hsharp
  have hd1 : l1 / l7l = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    field_simp [hl1, hl7l]
    norm_num
    linear_combination -h17
  have hcross : (8 / 9) * l1 / l1s = (3 : ℚ) ^ 5 / 2 ^ 8 := calc
    _ = (8 / 9) * (2048 * l1) / (2048 * l1s) := by
      field_simp
    _ = (8 / 9) * (2187 * l1s) / (2048 * l1s) := by
      rw [← hsharp]
    _ = (8 / 9) * (2187 / 2048) := by
      field_simp [hl1s]
    _ = (3 : ℚ) ^ 5 / 2 ^ 8 := by
      norm_num
  have hd2 : l2 / l1s = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h2v : l2 = (8 / 9) * l1 := by
      field_simp [hl2]
      linear_combination h2p
    simpa [h2v] using hcross
  have hd3 : l3 / l2s = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h3v : l3 = (8 / 9) * l2 := by
      field_simp [hl3]
      linear_combination h32
    have h2v : l2 = (8 / 9) * l1 := by
      field_simp [hl2]
      linear_combination h2p
    have h2sv : l2s = (8 / 9) * l1s := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h3v, h2v, h2sv]
    field_simp [hl1, hl1s]
    linear_combination -hsharp
  have hd4 : l4 / l3 = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h4v : l4 = (3 / 4) * l1 := by
      field_simp [hl4]
      linear_combination h4p
    have h3v : l3 = (64 / 81) * l1 := by
      field_simp [hl3]
      linear_combination h31
    rw [h4v, h3v]
    field_simp [hl1, hl3]
    norm_num
  have hd5 : l5 / l4s = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h5v : l5 = (2 / 3) * l1 := by
      field_simp [hl5']
      linear_combination g5
    have h4sv : l4s = (3 / 4) * l1s := by
      field_simp [hl4s]
      linear_combination h4s
    rw [h5v, h4sv]
    field_simp [hl1, hl1s]
    linear_combination -hsharp
  have hd6 : l6 / l5s = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h6v : l6 = (3 / 4) * l3 := by
      field_simp [hl6']
      linear_combination h63
    have h3v : l3 = (64 / 81) * l1 := by
      field_simp [hl3]
      linear_combination h31
    have h5sv : l5s = (2 / 3) * l1s := by
      field_simp [hl5s']
      linear_combination g5s
    rw [h6v, h3v, h5sv]
    convert hcross using 1
    ring
  have hd7 : l7 / l6s = (3 : ℚ) ^ 5 / 2 ^ 8 := by
    have h7v : l7 = (2 / 3) * l3 := by
      field_simp [hl7]
      linear_combination g7
    have h3v : l3 = (64 / 81) * l1 := by
      field_simp [hl3]
      linear_combination h31
    have h6sv : l6s = (2 / 3) * l2s := by
      field_simp [hl6s]
      linear_combination g6s
    have h2sv : l2s = (8 / 9) * l1s := by
      field_simp [hl2s]
      linear_combination h21s
    rw [h7v, h3v, h6sv, h2sv]
    convert hcross using 1
    ring
  refine ⟨⟨?_, ?_, ?_, ?_, hs6⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, hd7⟩, h2, h4⟩
  · simp [hs, hs2]
  · simp [hs2, hs4]
  · simp [hs4, hs5]
  · simp [hs5, hs6]
  · simp [hd1, hd2]
  · simp [hd2, hd3]
  · simp [hd3, hd4]
  · simp [hd4, hd5]
  · simp [hd5, hd6]
  · simp [hd6, hd7]


-- created on 2018-11-24
-- updated on 2026-10-26
