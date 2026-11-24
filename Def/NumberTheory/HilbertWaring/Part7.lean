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
public import Theorem.NumberTheory.HilbertWaring.Part5


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

def hwQuadraticMap (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a)
    (p : {p // p ∈ hwMomentFinset 4 N (hwPolyEval 2 a)}) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * (3 * c * N) + 1)) :=
  (fun i ↦ hwToCentered N ((p.1.1 i).val - (p.1.2 i).val)
      (hw_fin_sub_natAbs_le N (p.1.1 i) (p.1.2 i)),
    fun i ↦ hwToCentered (3 * c * N)
      (a 2 * ((p.1.1 i).val + (p.1.2 i).val) + a 1)
      (hw_quadratic_linear_natAbs_le c N a ha (p.1.1 i) (p.1.2 i)))

end MathlibExt.NumberTheory.HilbertWaringWanted
