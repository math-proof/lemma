/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

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
public import Abbrev.MeasureTheory.Geometry.BanachTarski

@[expose] public section

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Matrices to operators on the ambient space. -/
noncomputable def btToCLM :
    Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] (btE →L[ℝ] btE) :=
  Matrix.toEuclideanCLM

/-- The ambient isometry equivalence of a 3x3 real unitary (orthogonal) matrix. -/
noncomputable def btIsoOfUnitary (U : Matrix.unitaryGroup (Fin 3) ℝ) :
    btE ≃ᵢ btE :=
  (Unitary.linearIsometryEquiv
    ⟨btToCLM (U : Matrix (Fin 3) (Fin 3) ℝ),
      Unitary.map_mem btToCLM U.2⟩).toIsometryEquiv

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
