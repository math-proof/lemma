module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma r3legPi_norm {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : Quaternion.normSq (r3legPi hp3 w) = p :=
  (Classical.choose_spec (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)).1

lemma r3legPi_aligned {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) : r3legAligned p (r3legPi hp3 w) w :=
  (Classical.choose_spec (r3leg_aligned_norm_prime hp3 w w.property.1 w.property.2)).2

end MetaMathlibExt
