import sympy.matrices.confluent_vandermonde
import Lemma.Tensor.Dot.eq.SumMul__0
import torch.Tensor.sum
import Lemma.Tensor.Sum.of.Eq
open Tensor


@[main]
private lemma Comm
  [CommMagma α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [n]) :
-- imply
  X @ Y = Y @ X := by
-- proof
  rw [Dot.eq.SumMul__0]
  rw [Dot.eq.SumMul__0]
  apply Sum.of.Eq
  apply Nat.Mul.comm


@[main]
private lemma vandermonde.col_transform
  {n m d : ℕ} {x δ l : ℝ} :
-- imply
  (Matrix.of fun (i : Fin n) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) := by
-- proof
  exact Vandermonde.col_transform


@[main]
private lemma vandermonde.row_transform
  {n m d : ℕ} {x δ l : ℝ} :
-- imply
  (Matrix.of fun (i : Fin (m - d)) (j : Fin m) =>
      (-l) ^ ((d : ℤ) + (i : ℕ) - (j : ℕ)) * (if (i : ℕ) ≤ j then (d.choose ((j : ℕ) - i) : ℝ) else 0)) *
    (Matrix.of fun (i : Fin m) (j : Fin n) => x ^ (i : ℕ) * ((i : ℝ) + δ) ^ (j : ℕ)) =
    (Matrix.of fun (i : Fin (m - d)) (j : Fin n) => ((i : ℝ) + δ) ^ (j : ℕ) * x ^ (i : ℕ)) *
    (Matrix.of fun (i j : Fin n) => ((j : ℕ).choose i : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((j : ℤ) - (i : ℕ))) := by
-- proof
  exact Vandermonde.row_transform


-- created on 2020-08-16
-- updated on 2026-09-27
