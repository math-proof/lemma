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
public import Def.MeasureTheory.Geometry.BanachTarski.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Generator matrices unfold to explicit entries. -/
theorem btGenA_mat :
    (btGenA : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(3 : ℝ) / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1] :=
  rfl

theorem btGenB_mat :
    (btGenB : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(1 : ℝ), 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5] :=
  rfl

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
