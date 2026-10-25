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
import Def.MeasureTheory.Geometry.BanachTarski.Part4


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
