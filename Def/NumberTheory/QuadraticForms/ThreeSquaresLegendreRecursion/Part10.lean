module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def r3legPi {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : Quaternion ℤ :=
  Classical.choose (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)

end MetaMathlibExt
