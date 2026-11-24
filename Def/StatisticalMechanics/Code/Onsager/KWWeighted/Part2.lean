module
public import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
public import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
public import Theorem.StatisticalMechanics.Code.Onsager.KWWeighted


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_KWmatWeightedPhase (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    ons_dirPhase u v d1.2 * ons_KWmatWeighted L weight omega d2 d1

end StatMech.Onsager
