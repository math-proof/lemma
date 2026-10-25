/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Theorem.MathlibExtTest.Combinatorics.FractalSequenceTest.Part4


namespace MetaMathlibExt

def diagonalSequence (n : ℕ) : ℕ := (diagUnpair n).1 + 1

def diagonalFractal : FractalSequence where
  seq := diagonalSequence
  seq_pos := by intro n; simp [diagonalSequence]
  pos := diagPos
  pos_strict := diagPos_strict_right
  pos_sound := by intro i j; simp [diagonalSequence, diagUnpair_diagPos]
  pos_complete := by
    intro i n h
    refine ⟨(diagUnpair n).2, ?_⟩
    have hi : (diagUnpair n).1 = i := by simpa [diagonalSequence] using h
    rw [← hi, diagPos_diagUnpair]
  cond_F2 := by
    intro n i h
    let u := diagUnpair n
    have hu : u.1 = i + 1 := by simpa [u, diagonalSequence] using h
    have hn : diagPos u.1 u.2 = n := by simpa [u] using diagPos_diagUnpair n
    refine ⟨diagPos i u.2, ?_, ?_⟩
    · rw [← hn, hu]
      exact diagPos_strict_left u.2 (Nat.lt_succ_self i)
    · simp [diagonalSequence, diagUnpair_diagPos]
  cond_F3 := by
    intro h i j hhi
    let k := j + i - h + 1
    refine ⟨k, ?_, ?_⟩
    · dsimp only [k]
      simp only [diagPos]
      rw [show h + (j + i - h + 1) = (i + j) + 1 by omega, triangle_succ]
      rw [show i + (j + 1) = (i + j) + 1 by omega, triangle_succ]
      omega
    · intro l hl
      have hkpos : 0 < k := by simp [k]
      have hprev : diagPos h (k - 1) ≤ diagPos i j := by
        simp only [diagPos]
        rw [show h + (k - 1) = i + j by dsimp only [k]; omega]
        omega
      have hnext : diagPos i (j + 1) ≤ diagPos h (k + 1) := by
        change triangle (i + (j + 1)) + i ≤ triangle (h + (k + 1)) + h
        rw [show i + (j + 1) = (i + j) + 1 by omega,
          show h + (k + 1) = ((i + j) + 1) + 1 by dsimp only [k]; omega]
        rw [triangle_succ ((i + j) + 1), triangle_succ (i + j)]
        omega
      have hkl : k ≤ l := by
        by_contra hnot
        have hle : l ≤ k - 1 := by omega
        have := (diagPos_strict_right h).monotone hle
        omega
      have hlk : l ≤ k := by
        by_contra hnot
        have hle : k + 1 ≤ l := by omega
        have := (diagPos_strict_right h).monotone hle
        omega
      omega
  pos_column_strict := diagPos_strict_left

end MetaMathlibExt
