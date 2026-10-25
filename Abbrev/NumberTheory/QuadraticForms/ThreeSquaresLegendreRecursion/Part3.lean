/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part11


namespace MetaMathlibExt

abbrev r3legSqrtPairs (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p × ZMod p // z.1 ^ 2 = Δ * z.2 ^ 2}

abbrev r3legSqrts (p : ℕ) (Δ : ZMod p) :=
  {z : ZMod p // z ^ 2 = Δ}

end MetaMathlibExt
