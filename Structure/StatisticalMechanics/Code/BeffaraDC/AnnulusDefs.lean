/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part8
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

structure SymmetricDomain where
  
  u₁ : Site 2
  
  v₁ : Site 2
  
  u₂ : Site 2
  
  v₂ : Site 2
  
  γ₁ : LatticePath u₁ v₁
  
  γ₂ : LatticePath u₂ v₂
  
  isSymm : IsSymmetricPair γ₁ γ₂
  
  G : Set (Site 2)
  
  finite : G.Finite
  
  γ₁_subset : {z | z ∈ γ₁.support} ⊆ G
  
  γ₂_subset : {z | z ∈ γ₂.support} ⊆ G
  
  G_symm : diagReflFun '' G = G

end BeffaraDC
end StatMech
