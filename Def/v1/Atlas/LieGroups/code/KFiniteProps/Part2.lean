module
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Theorem.Complex.IsKFinite0
public import Theorem.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
public import Theorem.LinearMap.EqContinuousLinearEquivOfBijective.of.Bijective
public import Def.v1.Atlas.LieGroups.code.SchurLemma
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Class.v1.Atlas.LieGroups.code.KFiniteProps


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]

variable [CompactlySupportedMeasureAlgebra G M]

@[reducible]
def weakTopologyOnDiscreteMeasures :
    TopologicalSpace (MonoidAlgebra ℂ G) :=
  TopologicalSpace.induced
    (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)
    ‹TopologicalSpace M›

def IsKFiniteFunc (K : Subgroup G) (f : ↥K → ℂ) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun g : ↥K => fun k : ↥K => f (g⁻¹ * k))))

end Unitary
end ContinuousRep
end
