module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part20


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable instance r3legIncRepDecidable {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    DecidablePred (fun y : r3legRepType (p ^ 2 * n) => r3legInc hp3 w y) :=
  Classical.decPred _

end MetaMathlibExt
