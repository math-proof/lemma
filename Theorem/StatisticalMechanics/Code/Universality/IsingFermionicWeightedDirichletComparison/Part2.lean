/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part2
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedDirichletOperator_injective
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    Function.Injective
      (isingFiniteWeightedDirichletOperator conductance boundary) := by
  classical
  intro f g hfg
  have hopzero :
      isingFiniteWeightedDirichletOperator conductance boundary (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hboundary : ∀ x, boundary x → (f - g) x = 0 := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteWeightedLaplacian conductance (f - g) x) = 0 at h
    simpa [hx] using h
  have hharmonic :
      IsingFiniteWeightedHarmonicOn conductance boundary (f - g) := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteWeightedLaplacian conductance (f - g) x) = 0 at h
    simpa [hx] using h
  have hle : ∀ x, (f - g) x ≤ 0 := by
    apply isingFiniteWeighted_subharmonic_le_const
      G conductance boundary (f - g) 0 hconductance hpositive hhit
    · intro x hx
      exact (hharmonic x hx).ge
    · intro x hx
      exact (hboundary x hx).le
  have hge : ∀ x, 0 ≤ (f - g) x := by
    apply isingFiniteWeighted_const_le_superharmonic
      G conductance boundary (f - g) 0 hconductance hpositive hhit
    · intro x hx
      exact (hharmonic x hx).le
    · intro x hx
      exact (hboundary x hx).ge
  apply sub_eq_zero.mp
  funext x
  exact le_antisymm (hle x) (hge x)


theorem isingFiniteWeighted_exists_harmonic_extension
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (data : V → Real) :
    ∃ harmonic : V → Real,
      IsingFiniteWeightedHarmonicOn conductance boundary harmonic ∧
        ∀ x, boundary x → harmonic x = data x := by
  classical
  let rhs : V → Real := fun x ↦ if boundary x then data x else 0
  have hsurj : Function.Surjective
      (isingFiniteWeightedDirichletOperator conductance boundary) :=
    LinearMap.injective_iff_surjective.mp
      (isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit)
  obtain ⟨harmonic, hharmonic⟩ := hsurj rhs
  refine ⟨harmonic, ?_, ?_⟩
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteWeightedLaplacian conductance harmonic x) = rhs x at h
    simpa [rhs, hx] using h
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteWeightedLaplacian conductance harmonic x) = rhs x at h
    simpa [rhs, hx] using h


end
end StatMech.Universality
