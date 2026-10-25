/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5


namespace StatMech.Universality

open Complex

open HexWalk


namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


def slotTurns (E : HexVertexEnumeration region a h0 v du) :
    ((E.pairs × Bool) ⊕ (E.triplets × Fin 3)) → List ℤ
  | Sum.inl (P, false) => E.pairBase P ++ E.pairLq P
  | Sum.inl (P, true)  => E.pairBase P ++ E.pairLr P
  | Sum.inr (T, ⟨0, _⟩) => E.tripBase T
  | Sum.inr (T, ⟨1, _⟩) => E.tripBase T ++ [-1]
  | Sum.inr (T, _)      => E.tripBase T ++ [1]


end HexVertexEnumeration
end StatMech.Universality
