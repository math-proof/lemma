/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotient.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic
import Def.NumberTheory.PrimeCounting.SquarefreeTotient


namespace MathlibExt.NumberTheory.PrimeCounting

instance (n : ℕ) : Decidable (btSmallSquarefree n) := by
  unfold btSmallSquarefree
  infer_instance

end MathlibExt.NumberTheory.PrimeCounting
