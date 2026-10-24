/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanCatalanHankel.lean -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MetaMathlibExt
section
private def tri : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => 2 * tri n 0 + tri n 1
  | n + 1, k + 1 => tri n k + 2 * tri n (k + 1) + tri n (k + 2)

private def dot (i j : ℕ) : ℤ := ∑ k ∈ Finset.range (i + j + 1), tri i k * tri j k

private def Lmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => tri i.val j.val

private def Tmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.val = j.val then 3
  else if i.val + 1 = j.val then 1
  else if j.val + 1 = i.val then 1
  else 0
end
end MetaMathlibExt
