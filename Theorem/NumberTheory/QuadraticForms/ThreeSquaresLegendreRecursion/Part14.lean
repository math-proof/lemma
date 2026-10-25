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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part16


namespace MetaMathlibExt

lemma r3leg_q_rot {R : Type*} [CommSemiring R] (x : (R × R) × R) :
    r3legQ (r3legRot x) = r3legQ x := by
  change x.1.2 ^ 2 + x.2 ^ 2 + x.1.1 ^ 2 =
    x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2
  ring

lemma r3leg_b_rot {R : Type*} [CommSemiring R] (x y : (R × R) × R) :
    r3legB (r3legRot x) (r3legRot y) = r3legB x y := by
  change x.1.2 * y.1.2 + x.2 * y.2 + x.1.1 * y.1.1 =
    x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2
  ring

end MetaMathlibExt
