module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
public import Theorem.Nat.PrimeCounting.WeightedLargeSieve
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic
public import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MathlibExt.NumberTheory.PrimeCounting

@[simp] theorem btFareyMk_num {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.1.1 = a := rfl

@[simp] theorem btFareyMk_den {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.2.1 = r := rfl

end MathlibExt.NumberTheory.PrimeCounting
