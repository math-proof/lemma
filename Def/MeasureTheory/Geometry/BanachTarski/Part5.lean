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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
