module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Def.Combinatorics.Schnirelmann
public import Theorem.Finset.Schnirelmann
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic
public import Def.NumberTheory.HilbertWaring.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/
namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_fin_sub_natAbs_le (N : ℕ) (x y : Fin (N + 1)) :
    ((x.val : ℤ) - y.val).natAbs ≤ N := by
  by_cases hxy : x.val ≤ y.val
  · rw [Int.natAbs_natCast_sub_natCast_of_le hxy]
    have hy := y.isLt
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_not_ge hxy)]
    have hx := x.isLt
    omega

lemma hw_quadratic_linear_natAbs_le (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a) (x y : Fin (N + 1)) :
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤ 3 * c * N := by
  have ha₂ : (a 2).natAbs ≤ c := by
    simpa [hwCoeffBound] using ha (2 : Fin 3)
  have ha₁ : (a 1).natAbs ≤ c * N := by
    simpa [hwCoeffBound] using ha (1 : Fin 3)
  have hxy : (((x.val : ℤ) + y.val).natAbs) ≤ 2 * N := by
    rw [show (x.val : ℤ) + y.val = ((x.val + y.val : ℕ) : ℤ) by norm_num,
      Int.natAbs_natCast]
    omega
  calc
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤
        (a 2 * ((x.val : ℤ) + y.val)).natAbs + (a 1).natAbs :=
      Int.natAbs_add_le _ _
    _ = (a 2).natAbs * ((x.val : ℤ) + y.val).natAbs + (a 1).natAbs := by
      rw [Int.natAbs_mul]
    _ ≤ c * (2 * N) + c * N := Nat.add_le_add (Nat.mul_le_mul ha₂ hxy) ha₁
    _ = 3 * c * N := by ring

end MathlibExt.NumberTheory.HilbertWaringWanted
