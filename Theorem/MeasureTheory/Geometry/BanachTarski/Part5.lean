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
import Def.MeasureTheory.Geometry.BanachTarski.Part5


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Action composition and identity. -/
theorem btAct_mul (w v : FreeGroup (Fin 2)) (x : btE) :
    btAct (w * v) x = btAct w (btAct v x) := by
  simp only [btAct, map_mul, btIsoOfUnitary_mul]

theorem btAct_one (x : btE) : btAct 1 x = x := by
  simp only [btAct, map_one, btIsoOfUnitary_one]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
