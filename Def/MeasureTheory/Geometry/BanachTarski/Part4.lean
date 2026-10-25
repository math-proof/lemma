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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part3


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-! ## Free group generators and the integer model -/

/-- First generator: z-rotation by `arccos (3 / 5)`. -/
noncomputable def btGenA : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![(3 : ℝ) / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1],
    btRotBlock_mem ((3 : ℝ) / 5) (4 / 5) (by norm_num)⟩

/-- Second generator: x-rotation by `arccos (3 / 5)`. -/
noncomputable def btGenB : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![(1 : ℝ), 0, 0; 0, 3 / 5, -(4 / 5); 0, 4 / 5, 3 / 5],
    btRotBlockX_mem ((3 : ℝ) / 5) (4 / 5) (by norm_num)⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
