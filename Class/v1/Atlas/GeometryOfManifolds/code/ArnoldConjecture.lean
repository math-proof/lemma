/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Def.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture
set_option autoImplicit false

open DifferentialFormSpace


/-- The fixed-point set $\mathrm{Fix}(\varphi)$ of a Hamiltonian diffeomorphism, exposed as a
finite indexing type with evaluation $\mathrm{ev}_x(g) = g(x)$ satisfying $\mathrm{ev}_x(\varphi^* g)
= \mathrm{ev}_x(g)$. -/
class HasFixedPoints
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S) where
  FixedPoint : Type
  [fintype : Fintype FixedPoint]
  eval : FixedPoint → Ω 0 → ℝ
  eval_pullback_eq : ∀ (x : FixedPoint) (g : Ω 0),
    eval x (f.φ.pullback g) = eval x g

/-- Nondegeneracy of fixed points: the evaluation map on $\mathrm{Fix}(\varphi)$ is injective,
i.e. distinct fixed points are separated by smooth functions. -/
class IsNondegenerate
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    extends HasFixedPoints S f where
  eval_injective : Function.Injective eval


/-- A graded cohomology theory $H^k(M, \mathbb{R})$ taking finite-dimensional real values. -/
class HasCohomology
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  H : ℕ → Type*
  H_addCommGroup : ∀ k, AddCommGroup (H k)
  H_module : ∀ k, Module ℝ (H k)
  H_finiteDimensional : ∀ k, FiniteDimensional ℝ (H k)

