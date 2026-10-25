/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- Floer's isomorphism (graded): $HF^i(M, \varphi) \cong H^i(M, \mathbb{R})$ for a Hamiltonian
diffeomorphism on a compact symplectic manifold, hence Arnold's lower bound
$\#\mathrm{Fix}(\varphi) \ge \sum_i b_i(M)$. -/
structure FloerComplexGradedRank
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    {f : HamiltonianDiffeomorphism S}
    [hnd : IsNondegenerate S f]
    [hbetti : @HasBettiNumbers Ω VF inst]
    (FC : FloerComplex S f) where
  rankCF : ℕ → ℕ
  rankCF_sum : (Finset.range (hbetti.manifoldDim + 1)).sum rankCF = FC.totalRank
  rankCF_vanish : ∀ i, hbetti.manifoldDim < i → rankCF i = 0


/-- A compact Lagrangian submanifold $L \hookrightarrow (M, \omega)$: the pullback of $\omega$ to
$L$ vanishes, $\iota^* \omega = 0$. -/
structure CompactLagrangian
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (S : SymplecticManifold Ω_M VF_M) where
  Ω_L : ℕ → Type*
  VF_L : Type*
  [inst_L : DifferentialFormSpace Ω_L VF_L]
  inclusion : DFSMorphism Ω_L VF_L Ω_M VF_M
  lagrangian : inclusion.pullback S.ω = 0

