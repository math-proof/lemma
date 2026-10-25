/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Structure.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part3
set_option autoImplicit false

open DifferentialFormSpace


attribute [instance] CompactLagrangian.inst_L


/-- Data for the Lagrangian Arnold conjecture: cohomology of $L$, dimension, total Betti number
$\sum_i b_i(L) \ge 2$, and the intersection number $\# (L \cap \psi(L))$. -/
class HasLagrangianIntersectionData
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S)
    (ψ : HamiltonianDiffeomorphism S) where
  numIntersections : ℕ
  H_L : ℕ → Type*
  H_L_addCommGroup : ∀ k, AddCommGroup (H_L k)
  H_L_module : ∀ k, Module ℝ (H_L k)
  H_L_finiteDimensional : ∀ k, FiniteDimensional ℝ (H_L k)
  lagrangianDim : ℕ
  totalBettiL : ℕ
  totalBettiL_eq : totalBettiL = (Finset.range (lagrangianDim + 1)).sum
    (fun i => @Module.finrank ℝ (H_L i) _ (H_L_addCommGroup i).toAddCommMonoid (H_L_module i))
  betti_ge_two : totalBettiL ≥ 2

/-- Vanishing of Betti numbers of $L$ above its dimension: $b_i(L) = 0$ for $i > \dim L$. -/
class IsTransverseIntersection
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S)
    (ψ : HamiltonianDiffeomorphism S) : Prop where
  jointly_spanning : ∀ (α : Ω_M 1),
    L.inclusion.pullback α = (0 : L.Ω_L 1) →
    L.inclusion.pullback (ψ.φ.pullback α) = (0 : L.Ω_L 1) →
    α = 0

/-- Relative spin condition on $L \subset M$: existence of a closed 2-form $\beta$ on $M$ whose
pullback to $L$ is exact, used to orient moduli spaces in Lagrangian Floer theory. -/
class IsRelativelySpin
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S) : Prop where
  spin_lift : ∃ (β : Ω_M 2),
    inst_M.d β = 0 ∧
    ∃ (γ : L.Ω_L 1), L.inclusion.pullback β = L.inst_L.d γ

/-- $H^1$-injectivity hypothesis: every closed 1-form on $L$ lifts to a closed 1-form on $M$ up
to an exact form, ensuring the inclusion $H^1(M) \to H^1(L)$ is surjective on representatives. -/
class HasH1Injectivity
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M)
    (L : CompactLagrangian S) : Prop where
  h1_surjective : ∀ (α : L.Ω_L 1),
    L.inst_L.d α = 0 →
    ∃ (β : Ω_M 1), inst_M.d β = 0 ∧
      ∃ (γ : L.Ω_L 0), L.inclusion.pullback β = α + L.inst_L.d γ

