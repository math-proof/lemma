/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
import Lemma.Nat.PrimeCounting.WeightedLargeSieve
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve.Part2
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

@[simp] theorem btFareyMk_num {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.1.1 = a := rfl

@[simp] theorem btFareyMk_den {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.2.1 = r := rfl

end MathlibExt.NumberTheory.PrimeCounting
