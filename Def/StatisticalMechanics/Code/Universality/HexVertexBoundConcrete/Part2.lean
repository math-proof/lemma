/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexVBC_adjClosure (a : ℂ) (h0 : ℤ) : Finset ℂ :=
  hexVBC_star a (halfStep h0) ∪ hexVBC_star (hexConcreteQ a h0) (halfStep h0)
    ∪ hexVBC_star (hexConcreteR a h0) (halfStep h0)


end StatMech.Universality
