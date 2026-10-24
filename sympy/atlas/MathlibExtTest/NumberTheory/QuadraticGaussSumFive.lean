/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QuadraticGaussSumFive.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark (Muse Spark 1.3)
-/

import sympy.atlas.NumberTheory.QuadraticGaussSumFive
import Lemma.Nat.QuadraticGaussSumFive
import Mathlib.Tactic

namespace MetaMathlibExt

open scoped MetaMathlibExt

-- Positive residues through the public evaluation theorem.
example : quadraticGaussSum5 1 = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (1 : ℤ) = 1 := by norm_num
  rw [quadraticGaussSum5_eval 1 (by decide), hleg]
  simp

example : quadraticGaussSum5 2 = -((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (2 : ℤ) = -1 := by norm_num
  rw [quadraticGaussSum5_eval 2 (by decide), hleg]
  simp

example : quadraticGaussSum5 4 = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (4 : ℤ) = 1 := by norm_num
  rw [quadraticGaussSum5_eval 4 (by decide), hleg]
  simp

-- Negative residues: `(-1 / 5) = 1` and `(-2 / 5) = -1`.
example : quadraticGaussSum5 (-1) = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (-1 : ℤ) = 1 := by norm_num
  rw [quadraticGaussSum5_eval (-1) (by decide), hleg]
  simp

example : quadraticGaussSum5 (-2) = -((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (-2 : ℤ) = -1 := by norm_num
  rw [quadraticGaussSum5_eval (-2) (by decide), hleg]
  simp

-- Periodicity via the integer-facing API: `6 ≡ 1` and `-4 ≡ 1` mod five.
example : quadraticGaussSum5 6 = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (6 : ℤ) = 1 := by norm_num
  rw [quadraticGaussSum5_eval 6 (by decide), hleg]
  simp

example : quadraticGaussSum5 (-4) = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hleg : legendreSym 5 (-4 : ℤ) = 1 := by norm_num
  rw [quadraticGaussSum5_eval (-4) (by decide), hleg]
  simp

end MetaMathlibExt
