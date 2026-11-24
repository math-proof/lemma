module
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
public import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


abbrev SlotType (E : HexVertexEnumeration region a h0 v du) : Type :=
  (E.pairs × Bool) ⊕ (E.triplets × Fin 3)


end StatMech.Universality
