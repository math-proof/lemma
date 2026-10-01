import sympy.Basic
import Mathlib.Data.Matrix.Block


@[main]
private lemma main
  [Fintype l] [Fintype m] [Fintype n]
  [CommRing α]
  {A : Matrix l m α} {B : Matrix m n α} {X : Matrix l n α}
  {C : Matrix l' m' α} {D : Matrix m' n' α} {Y : Matrix l' n' α}
  [Fintype m']
-- given
  (h₀ : A * B = X)
  (h₁ : C * D = Y) :
-- imply
  Matrix.fromBlocks A 0 0 C * Matrix.fromBlocks B 0 0 D = Matrix.fromBlocks X 0 0 Y := by
-- proof
  rw [Matrix.fromBlocks_multiply, ← h₀, ← h₁]
  simp


-- created on 2023-09-16
