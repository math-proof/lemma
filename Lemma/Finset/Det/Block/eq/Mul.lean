import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import sympy.matrices.block_swap
import Lemma.Matrix.DetSq_FromBlocks0.eq.MulMulPowNeg1_DetDet
import Lemma.Matrix.DetSq_FromBlocks_0.eq.MulMulPowNeg1_DetDet
open Matrix


@[path]
private lemma main
  [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : Matrix m m R}
  {B : Matrix m n R}
  {D : Matrix n n R} :
-- imply
  (Matrix.fromBlocks A B 0 D).det = A.det * D.det :=
-- proof
  Matrix.det_fromBlocks_zero₂₁ A B D


@[path]
private lemma lower
  [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : Matrix m m R}
  {C : Matrix n m R}
  {D : Matrix n n R} :
-- imply
  (Matrix.fromBlocks A 0 C D).det = A.det * D.det :=
-- proof
  Matrix.det_fromBlocks_zero₁₂ A C D


@[path]
private lemma anti_diagonal
  [CommRing R]
  {a b : ℕ}
  {A : Matrix (Fin a) (Fin a) R}
  {C : Matrix (Fin b) (Fin b) R}
  {D : Matrix (Fin b) (Fin a) R} :
-- imply
  (Matrix.BlockSwap.sq (Matrix.fromBlocks 0 A C D)).det = (-1) ^ (a * b) * A.det * C.det :=
-- proof
  DetSq_FromBlocks0.eq.MulMulPowNeg1_DetDet A C D


@[path]
private lemma anti_diagonal.lower
  [CommRing R]
  {a b : ℕ}
  {B : Matrix (Fin a) (Fin b) R}
  {A : Matrix (Fin a) (Fin a) R}
  {C : Matrix (Fin b) (Fin b) R} :
-- imply
  (Matrix.BlockSwap.sq (Matrix.fromBlocks B A C 0)).det = (-1) ^ (a * b) * A.det * C.det :=
-- proof
  DetSq_FromBlocks_0.eq.MulMulPowNeg1_DetDet B A C


-- created on 2021-11-21
