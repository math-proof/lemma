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
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part19


namespace MetaMathlibExt

noncomputable def r3leg_scaleRepEquiv {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ) :
    r3legRepType n ≃
      {y : r3legRepType (p ^ 2 * n) // r3legRed p (y : r3legIntVec) = 0} where
  toFun x := ⟨⟨r3legScale p x, r3leg_mem_rep.mpr (by
    rw [r3leg_q_scale, r3leg_mem_rep.mp x.2]
    push_cast
    ring)⟩, by
      rw [r3leg_red_scale]
      change ((p : ℤ) : ZMod p) • r3legRed p x = 0
      simp⟩
  invFun y := ⟨r3legVecDiv y p, r3leg_mem_rep.mpr (by
    have hdiv : r3legVecDvd (p : ℤ) y :=
      (r3leg_vecDvd_iff_red_eq_zero p y).mpr y.2
    have hscale : r3legScale p (r3legVecDiv y p) = y := r3leg_scale_vecDiv hdiv
    have hq := congrArg r3legQ hscale
    rw [r3leg_q_scale, r3leg_mem_rep.mp y.1.2] at hq
    push_cast at hq
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
    nlinarith)⟩
  left_inv x := by
    apply Subtype.ext
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    apply r3leg_scale_left_cancel hpne
    exact r3leg_scale_vecDiv
      ⟨⟨(x : r3legIntVec).1.1, rfl⟩, ⟨(x : r3legIntVec).1.2, rfl⟩,
        (x : r3legIntVec).2, rfl⟩
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact r3leg_scale_vecDiv ((r3leg_vecDvd_iff_red_eq_zero p y).mpr y.2)

end MetaMathlibExt
