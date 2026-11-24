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
public import Def.MeasureTheory.Geometry.BanachTarski.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Action composition and identity. -/
theorem btAct_mul (w v : FreeGroup (Fin 2)) (x : btE) :
    btAct (w * v) x = btAct w (btAct v x) := by
  simp only [btAct, map_mul, btIsoOfUnitary_mul]

theorem btAct_one (x : btE) : btAct 1 x = x := by
  simp only [btAct, map_one, btIsoOfUnitary_one]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
