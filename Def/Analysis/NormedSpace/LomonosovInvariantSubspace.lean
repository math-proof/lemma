/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Theorem.Analysis.NormedSpace.LomonosovInvariantSubspace

@[expose] public section

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
