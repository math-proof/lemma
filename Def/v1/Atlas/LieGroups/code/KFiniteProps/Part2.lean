/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Lemma.Complex.IsKFinite0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Class.v1.Atlas.LieGroups.code.KFiniteProps


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
