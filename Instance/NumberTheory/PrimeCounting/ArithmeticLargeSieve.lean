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
import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable instance (z : ℕ) : Fintype (btFareyIndex z) := by
  classical
  unfold btFareyIndex
  infer_instance

end MathlibExt.NumberTheory.PrimeCounting
