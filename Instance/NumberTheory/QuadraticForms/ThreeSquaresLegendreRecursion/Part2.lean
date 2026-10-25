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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part20


namespace MetaMathlibExt

noncomputable instance r3legIncRepDecidable {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) :
    DecidablePred (fun y : r3legRepType (p ^ 2 * n) => r3legInc hp3 w y) :=
  Classical.decPred _

end MetaMathlibExt
