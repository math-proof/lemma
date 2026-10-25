/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization


namespace StatMech.Universality

open Complex HexWalk


noncomputable def normalizedParafObservable (inRegion : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (sigma x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * parafObservable inRegion a h0 z sigma x


end StatMech.Universality
