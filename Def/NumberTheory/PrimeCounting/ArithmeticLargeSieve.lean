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
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

def btFareyIndex (z : ℕ) :=
  {p : Fin (z + 1) × Fin (z + 1) //
    0 < p.2.1 ∧ p.1.1 < p.2.1 ∧ Nat.Coprime p.1.1 p.2.1}

end MathlibExt.NumberTheory.PrimeCounting
