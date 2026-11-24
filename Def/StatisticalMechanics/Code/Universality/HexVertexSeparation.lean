module
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
public import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean -/
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


def PassesThrough (a : ℂ) (h0 : ℤ) (ts : List ℤ) (z : ℂ) : Prop :=
  z ∈ (ofTurns a h0 ts).mids


end StatMech.Universality
