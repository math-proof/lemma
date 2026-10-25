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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part16


namespace MetaMathlibExt

def r3leg_primitiveUnitMap {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    (ZMod p)ˣ → {w : r3legIso p // r3legInc hp3 w y} := by
  let v := r3legRed p y
  have hvne : v ≠ 0 := hyne
  have hvq : r3legQ v = 0 := by
    dsimp [v]
    rw [r3leg_q_red, hyq]
    push_cast
    simp
  intro u
  let w : r3legIso p :=
    ⟨(u : ZMod p) • v, smul_ne_zero (Units.ne_zero u) hvne, by
      rw [r3leg_q_smul, hvq, mul_zero]⟩
  refine ⟨w, (r3leg_inc_primitive_iff hp3 w y hyq hyne).2 ?_⟩
  refine ⟨((u⁻¹ : (ZMod p)ˣ) : ZMod p), Units.ne_zero u⁻¹, ?_⟩
  change v = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • ((u : ZMod p) • v)
  rw [smul_smul, Units.inv_mul, one_smul]

end MetaMathlibExt
