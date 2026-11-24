module
public import Theorem.StatisticalMechanics.Code.Onsager.KWWeighted.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.FirstReturnScale


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators

def ons_scaleEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ) :
    Sym2 (ZMod L × ZMod L) → ℂ :=
  fun f => if f = edge then t * weight f else weight f

end StatMech.Onsager
