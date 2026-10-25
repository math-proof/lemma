/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexVBCRegion (a : ℂ) (h0 : ℤ) : HexFiniteRegion where
  verts := hexVBC_adjClosure a h0
  mids := {a, hexConcreteQ a h0, hexConcreteR a h0}
  start := a
  start_mem := by simp
  vertexBound := hexVBC_vertexBound a h0


end StatMech.Universality
