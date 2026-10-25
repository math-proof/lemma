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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part4


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The two generators as a function on `Fin 2`. -/
noncomputable def btGenFun : Fin 2 → Matrix.unitaryGroup (Fin 3) ℝ :=
  ![btGenA, btGenB]

/-- The homomorphism from the free group of rank 2 to rotations. -/
noncomputable def btRho : FreeGroup (Fin 2) →* Matrix.unitaryGroup (Fin 3) ℝ :=
  FreeGroup.lift btGenFun

/-- The action of a free group word as an ambient isometry. -/
noncomputable def btAct (w : FreeGroup (Fin 2)) : btE ≃ᵢ btE :=
  btIsoOfUnitary (btRho w)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
