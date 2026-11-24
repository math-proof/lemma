module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma r3leg_q_red (p : ℕ) (x : r3legIntVec) :
    r3legQ (r3legRed p x) = ((r3legQ x : ℤ) : ZMod p) := by
  simp [r3legQ, r3legRed]

lemma r3leg_q_smul {R : Type*} [CommSemiring R] (c : R) (x : (R × R) × R) :
    r3legQ (c • x) = c ^ 2 * r3legQ x := by
  simp [r3legQ]
  ring

end MetaMathlibExt
