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
import Def.MeasureTheory.Geometry.BanachTarski.Part8


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Unfolding the axis choice at a nontrivial word. -/
theorem btU_eq (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    btU w = Classical.choose (btAxis w hw) := by
  simp only [btU, dite_eq_right hw]

/-- The chosen axis is a unit vector. -/
theorem btU_dot (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    dotProduct (btU w) (btU w) = 1 := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).1

/-- The chosen axis has `(u 0, u 2) ≠ (0, 0)`. -/
theorem btU_nz (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    (btU w 0, btU w 2) ≠ (0, 0) := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).2.1

/-- Fixed points of `btAct w` lie on the chosen axis. -/
theorem btU_fix (w : FreeGroup (Fin 2)) (hw : w ≠ 1)
    (x : btE) (hx : btAct w x = x) :
    ∃ s : ℝ, WithLp.ofLp x = s • btU w := by
  rw [btU_eq w hw]
  exact (Classical.choose_spec (btAxis w hw)).2.2 x hx

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
