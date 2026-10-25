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


noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section KStability

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

theorem kFiniteSubspace_stable (π : ContinuousRep G V) (K : Subgroup G)
    (g : K) (v : V) (hv : v ∈ kFiniteSubspace π K) :
    (π.toMonoidHom g) v ∈ kFiniteSubspace π K := by
  rw [mem_kFiniteSubspace] at hv ⊢
  unfold IsKFinite at *
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) ((π.toMonoidHom g) v))) ≤
      Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx
    show (π.toMonoidHom k) ((π.toMonoidHom g) v) ∈
      (Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) : Set V)
    have heq : (π.toMonoidHom k) ((π.toMonoidHom g) v) =
        (π.toMonoidHom ((k : G) * (g : G))) v := by
      rw [← ContinuousLinearMap.mul_apply]; congr 1
      exact (π.toMonoidHom.map_mul (k : G) (g : G)).symm
    rw [heq]
    exact Submodule.subset_span ⟨⟨(k : G) * (g : G), K.mul_mem k.2 g.2⟩, rfl⟩
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

end KStability

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unitary_adjoint_eq_inv (π : ContinuousRep G E) (hU : π.IsUnitary)
    (g : G) :
    ContinuousLinearMap.adjoint (π.toMonoidHom g) = π.toMonoidHom g⁻¹ := by
  have h1 := (hU g).1
  have hginv : π.toMonoidHom g * π.toMonoidHom g⁻¹ = 1 := by
    rw [← map_mul]; simp
  calc ContinuousLinearMap.adjoint (π.toMonoidHom g)
      = ContinuousLinearMap.adjoint (π.toMonoidHom g) * 1 := (mul_one _).symm
    _ = ContinuousLinearMap.adjoint (π.toMonoidHom g) *
        (π.toMonoidHom g * π.toMonoidHom g⁻¹) := by rw [hginv]
    _ = (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) *
        π.toMonoidHom g⁻¹ := (mul_assoc _ _ _).symm
    _ = 1 * π.toMonoidHom g⁻¹ := by rw [h1]
    _ = π.toMonoidHom g⁻¹ := one_mul _

end Unitary
end ContinuousRep
end
