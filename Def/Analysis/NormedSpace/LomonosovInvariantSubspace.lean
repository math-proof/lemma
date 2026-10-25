/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Theorem.Analysis.NormedSpace.LomonosovInvariantSubspace


namespace FunctionalAnalysis.LomonosovInvariantSubspaceWanted

/-- Centralizer subalgebra of `K` (N6 notation). -/
def lomoCentralizer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) : Subalgebra ℂ (E →L[ℂ] E) :=
  Subalgebra.centralizer ℂ {K}

/-- Orbit submodule: operators of the centralizer applied to `y` (N6 notation). -/
noncomputable def lomoOrb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y : E) : Submodule ℂ E :=
  Submodule.map (↑(ContinuousLinearMap.apply ℂ E y) : (E →L[ℂ] E) →ₗ[ℂ] E)
    (Subalgebra.toSubmodule (lomoCentralizer K))

/-- Closed orbit: topological closure of the orbit (N6 notation). -/
noncomputable def lomoOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y : E) : Submodule ℂ E :=
  (lomoOrb K y).topologicalClosure

end FunctionalAnalysis.LomonosovInvariantSubspaceWanted
