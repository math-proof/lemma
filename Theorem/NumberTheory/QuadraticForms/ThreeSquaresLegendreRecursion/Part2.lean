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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part2


namespace MetaMathlibExt

lemma r3leg_red_scale (p : ℕ) (c : ℤ) (x : r3legIntVec) :
    r3legRed p (r3legScale c x) = (c : ZMod p) • r3legRed p x := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legScale]
  · simp [r3legRed, r3legScale]

lemma r3leg_aligned_transfer {p : ℕ} [Fact (Nat.Prime p)]
    {q q' r : Quaternion ℤ}
    {w : r3legModVec p} {c : ℤ} (hc : (c : ZMod p) ≠ 0)
    (hqr : c • q' = q * r) (hq : r3legAligned p q w) :
    r3legAligned p q' w := by
  intro x
  obtain ⟨t, ht⟩ := hq (r3legPhi r x)
  have hs : ((c : ZMod p) ^ 2) • r3legRed p (r3legPhi q' x) = t • w := by
    calc
      ((c : ZMod p) ^ 2) • r3legRed p (r3legPhi q' x) =
          r3legRed p (r3legScale (c ^ 2) (r3legPhi q' x)) := by
        rw [← Int.cast_pow]
        exact (r3leg_red_scale p (c ^ 2) (r3legPhi q' x)).symm
      _ = r3legRed p (r3legPhi (c • q') x) := by
        rw [r3leg_phi_smul]
      _ = r3legRed p (r3legPhi (q * r) x) := by rw [hqr]
      _ = r3legRed p (r3legPhi q (r3legPhi r x)) := by
        rw [r3leg_phi_comp]
      _ = t • w := ht
  refine ⟨(((c : ZMod p) ^ 2)⁻¹ * t), ?_⟩
  have hi := congrArg (fun v : r3legModVec p => ((c : ZMod p) ^ 2)⁻¹ • v) hs
  have hc2 : (c : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  simpa [smul_smul, hc2] using hi

end MetaMathlibExt
