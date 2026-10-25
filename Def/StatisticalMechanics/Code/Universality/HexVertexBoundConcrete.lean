/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexVBC_star (m s : ℂ) : Finset ℂ :=
  { m + (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * s,
    m + (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * s,
    m + (((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * s }


end StatMech.Universality
