module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Def.v1.Atlas.LieGroups.code.SchurLemma
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Def.v1.Atlas.LieGroups.code.KFiniteProps
public section

noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

class CompactlySupportedMeasureAlgebra
    (G : Type uG) [Group G] [TopologicalSpace G]
    (M : Type uM) [Ring M] [Algebra ℂ M] [TopologicalSpace M] where
  dirac : G →* M
  discrete_in_closure : ∀ (m : M),
    m ∈ closure (Set.range (MonoidAlgebra.lift ℂ M G dirac))
  total_variation_cont : ∀ (f : G → ℝ) (_hf : Continuous f) (_hf_nn : ∀ g, 0 ≤ f g),
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G dirac)
        ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.coeff.sum (fun g c => ‖c‖ * f g))

end Unitary
end ContinuousRep
end
