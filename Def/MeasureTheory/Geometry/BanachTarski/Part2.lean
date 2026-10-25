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
import Abbrev.MeasureTheory.Geometry.BanachTarski


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
