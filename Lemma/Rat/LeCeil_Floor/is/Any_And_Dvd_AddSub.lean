import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Int.LtToNat.is.Lt.of.Ge_0
import Lemma.Rat.In_Icc.of.Gt_0
open Int Rat


@[main, mp, mpr]
private lemma main
  [NeZero n]
  [NeZero (d : ℕ)]
-- given
  (l u i : ℕ) :
-- imply
  ⌈((↑(i - l) : ℤ) - (i - l)) / (d : ℚ)⌉ ≤ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - (i - l)) / (d : ℚ)⌋ ↔ ∃ j : Fin n, (j - i : ℤ) ∈ Icc (-l : ℤ) u ∧ (d : ℤ) ∣ (j - i : ℤ) + l := by
-- proof
  constructor
  ·
    intro h_icc
    let t := ⌈((↑(i - l) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌉
    have ht : t ∈ Icc ⌈((↑(i - l) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌉ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌋ := by
      rw [Set.mem_Icc]
      exact ⟨le_rfl, h_icc⟩
    have hj := (In_Icc.of.Gt_0 (d := d) (NeZero.pos d) n l u i t).mpr ht
    rw [Set.mem_Icc] at hj
    set j_z := (i : ℤ) - l + (d : ℤ) * t
    have hj0 : 0 ≤ j_z := by linarith [hj.1]
    have hn := NeZero.pos n
    let j : Fin n := ⟨j_z.toNat, (LtToNat.is.Lt.of.Ge_0 hj0 n).mpr (by omega)⟩
    refine ⟨j, ?_, ?_⟩
    ·
      grind
    ·
      have hj_cast : j = j_z := by simp [j, EqToNat.of.Ge_0 hj0]
      rw [hj_cast]
      use t
      omega
  ·
    rintro ⟨j, hband, hdvd⟩
    obtain ⟨t, ht⟩ := hdvd
    have ht_Icc := (In_Icc.of.Gt_0 (d := d) (NeZero.pos d) n l u i t).mp (by grind)
    rw [Set.mem_Icc] at ht_Icc
    exact ht_Icc.1.trans ht_Icc.2


-- created on 2026-07-28
