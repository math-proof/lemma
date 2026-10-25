/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexCoverage.lean -/

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


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


structure HexVertexComplete (E : HexVertexEnumeration region a h0 v du) : Prop where
  

  complete_p : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + du) →
    ∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T = ts
  


  complete_q : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
    (∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T ++ [-1] = ts)
      ∨ (∃ P : ℕ, P ∈ E.pairs ∧ E.pairBase P ++ E.pairLq P = ts)
  


  complete_r : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
    (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
    (∃ T : ℕ, T ∈ E.triplets ∧ E.tripBase T ++ [1] = ts)
      ∨ (∃ P : ℕ, P ∈ E.pairs ∧ E.pairBase P ++ E.pairLr P = ts)


end StatMech.Universality
