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
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part9
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

variable (D : SymmetricDomain)


theorem wired_subset : D.wired ⊆ D.G := by
  rintro z (hz | hz)
  · exact D.γ₁_subset hz
  · exact D.γ₂_subset hz


theorem free_subset : D.free ⊆ D.G := Set.diff_subset


theorem wired_union_free : D.wired ∪ D.free = D.G := by
  rw [free, Set.union_diff_cancel D.wired_subset]

theorem wired_disjoint_free : Disjoint D.wired D.free :=
  Set.disjoint_sdiff_right


theorem wired_finite : D.wired.Finite := D.finite.subset D.wired_subset


theorem wired_symm : diagReflFun '' D.wired = D.wired := by
  rw [wired, Set.image_union, D.isSymm, D.isSymm.symm, Set.union_comm]


end SymmetricDomain
end BeffaraDC
end StatMech
