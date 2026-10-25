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
import Def.MeasureTheory.Geometry.BanachTarski.Part9


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The inverse action undoes the action. -/
theorem btAct_inv (w : FreeGroup (Fin 2)) (x : btE) :
    btAct w⁻¹ (btAct w x) = x := by
  rw [← btAct_mul, inv_mul_cancel, btAct_one]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
