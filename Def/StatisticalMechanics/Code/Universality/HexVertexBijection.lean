/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


def slotLabel {E : HexVertexEnumeration region a h0 v du} :
    ((E.pairs × Bool) ⊕ (E.triplets × Fin 3)) → Fin 3
  | Sum.inl (_, false) => 1
  | Sum.inl (_, true)  => 2
  | Sum.inr (_, ⟨0, _⟩) => 0
  | Sum.inr (_, ⟨1, _⟩) => 1
  | Sum.inr (_, _)      => 2


noncomputable def labelMid (v du : ℂ) : Fin 3 → ℂ
  | ⟨0, _⟩ => v + du
  | ⟨1, _⟩ => v + hexOmega * du
  | _      => v + hexOmega ^ 2 * du


end StatMech.Universality
