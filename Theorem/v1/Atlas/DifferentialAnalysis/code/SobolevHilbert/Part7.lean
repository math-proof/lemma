/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Instance.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part5


noncomputable section

open MeasureTheory

namespace SobolevHilbert

attribute [local instance] sobolevSpace_nacg


/-- The Fourier-side identification of `SobolevSpace n m` with `L^2` (as a bare equivalence). -/
theorem schwartz_iteratedFDeriv_memLp {n m : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (⇑φ) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  set E := EuclideanSpace ℝ (Fin n)
  set g := fun x : E => iteratedFDeriv ℝ j (⇑φ) x
  have hcont : Continuous g :=
    φ.smooth'.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have htemp : (volume : Measure E).HasTemperateGrowth := inferInstance
  obtain ⟨k, hk⟩ := htemp.exists_eLpNorm_lt_top (p := 2)
  have h_one_add (x : E) : (0 : ℝ) < 1 + ‖x‖ := by positivity
  set B := 2 ^ k * (Finset.Iic (k, j)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) φ
  have hB : ∀ x : E, (1 + ‖x‖) ^ k * ‖g x‖ ≤ B :=
    fun x => SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, j)) le_rfl le_rfl φ x
  have hg_bound : ∀ x : E, ‖g x‖ ≤ B * (1 + ‖x‖) ^ (-(k : ℝ)) := by
    intro x
    have hpow_pos : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
    rw [Real.rpow_neg (h_one_add x).le, Real.rpow_natCast,
      mul_comm B, ← div_eq_inv_mul, le_div_iff₀ hpow_pos]
    linarith [hB x]
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  calc eLpNorm g 2 volume
      ≤ eLpNorm (fun x : E => B * (1 + ‖x‖) ^ (-(k : ℝ))) 2 volume :=
        eLpNorm_mono_real hg_bound
    _ < ⊤ := by
        have heq : (fun x : E => B * (1 + ‖x‖) ^ (-(k : ℝ))) =
            B • (fun x : E => (1 + ‖x‖) ^ (-(k : ℝ))) := by
          ext x; simp [Pi.smul_apply, smul_eq_mul]
        rw [heq, eLpNorm_const_smul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hk

end SobolevHilbert
end
