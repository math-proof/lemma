/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part15


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The ball duplicates. -/
theorem btCongr_ball_double :
    btCongr (Metric.closedBall (0 : btE) 1)
        (Metric.closedBall (0 : btE) 1 ∪ btShift '' Metric.closedBall (0 : btE) 1) ∧
      btShift '' Metric.closedBall (0 : btE) 1 = Metric.closedBall btC₂ 1 ∧
      Disjoint (Metric.closedBall (0 : btE) 1)
        (btShift '' Metric.closedBall (0 : btE) 1) := by
  have himg : btShift '' Metric.closedBall (0 : btE) 1 =
      Metric.closedBall btC₂ 1 := by
    have e : btShift (0 : btE) = btC₂ := by
      simp only [btShift, IsometryEquiv.addRight_apply, zero_add]
    rw [IsometryEquiv.image_closedBall, e]
  have hdisj : Disjoint (Metric.closedBall (0 : btE) 1)
      (btShift '' Metric.closedBall (0 : btE) 1) := by
    rw [himg]
    apply Metric.closedBall_disjoint_closedBall
    rw [btC₂_dist]
    norm_num
  have hBallOm : btCongr (Metric.closedBall (0 : btE) 1) btOmega :=
    btCongr_trans btCongr_ball_punctured btCongr_punctured_omega
  obtain ⟨h12, h34, hdisjQ, hunion⟩ := btOmega_halves
  have hQ12B : btCongr (btQ₁ ∪ btQ₂) (Metric.closedBall (0 : btE) 1) :=
    btCongr_trans h12 (btCongr_symm hBallOm)
  have hQ34S : btCongr (btQ₃ ∪ btQ₄)
      (btShift '' Metric.closedBall (0 : btE) 1) :=
    btCongr_trans h34
      (btCongr_trans (btCongr_symm hBallOm)
        (btCongr_self_image btShift (Metric.closedBall (0 : btE) 1)))
  have hOmDouble : btCongr btOmega
      (Metric.closedBall (0 : btE) 1 ∪
        btShift '' Metric.closedBall (0 : btE) 1) := by
    have hun := btCongr_union hQ12B hQ34S hdisjQ hdisj
    rw [hunion] at hun
    exact hun
  exact ⟨btCongr_trans hBallOm hOmDouble, himg, hdisj⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
