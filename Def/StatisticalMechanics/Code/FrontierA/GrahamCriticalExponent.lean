/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCriticalExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Filter Set


namespace StatMech.FrontierA

noncomputable def grahamExponentRatio (f : Real -> Real) (t : Real) : Real :=
  Real.log (f t) / Real.log t


def HasGrahamCriticalExponent (f : Real -> Real) (a : Real) : Prop :=
  Tendsto (grahamExponentRatio f) (nhdsWithin 0 (Ioi 0)) (nhds a)


end StatMech.FrontierA
