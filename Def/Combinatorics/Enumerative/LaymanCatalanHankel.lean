/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LaymanCatalanHankel.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

def tri : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => 2 * tri n 0 + tri n 1
  | n + 1, k + 1 => tri n k + 2 * tri n (k + 1) + tri n (k + 2)

def dot (i j : ℕ) : ℤ := ∑ k ∈ Finset.range (i + j + 1), tri i k * tri j k

def Lmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => tri i.val j.val

def Tmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.val = j.val then 3
  else if i.val + 1 = j.val then 1
  else if j.val + 1 = i.val then 1
  else 0

end
end MetaMathlibExt
