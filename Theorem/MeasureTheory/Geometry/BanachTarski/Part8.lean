module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Def.MeasureTheory.Geometry.BanachTarski.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
