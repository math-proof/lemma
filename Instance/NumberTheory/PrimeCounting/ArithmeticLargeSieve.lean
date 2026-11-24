module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
public import Theorem.Nat.PrimeCounting.WeightedLargeSieve
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic
public import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable instance (z : ℕ) : Fintype (btFareyIndex z) := by
  classical
  unfold btFareyIndex
  infer_instance

end MathlibExt.NumberTheory.PrimeCounting
