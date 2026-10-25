/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexVertexSeparated (E : HexVertexEnumeration region a h0 v du) : Prop where
  

  pairQ_count_three : ∀ P ∈ E.pairs,
    specialMidCount a h0 v du (E.pairBase P ++ E.pairLq P) = 3
  

  pairR_count_three : ∀ P ∈ E.pairs,
    specialMidCount a h0 v du (E.pairBase P ++ E.pairLr P) = 3
  

  tripQ_not_passes_r : ∀ T ∈ E.triplets,
    ¬ PassesThrough a h0 (E.tripBase T ++ [-1]) (v + hexOmega ^ 2 * du)
  

  tripR_not_passes_q : ∀ T ∈ E.triplets,
    ¬ PassesThrough a h0 (E.tripBase T ++ [1]) (v + hexOmega * du)


end StatMech.Universality
