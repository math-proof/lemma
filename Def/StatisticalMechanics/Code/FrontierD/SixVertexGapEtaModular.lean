/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEtaModular.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs.Part3
import Mathlib.NumberTheory.ModularForms.Discriminant
open Filter Topology Complex UpperHalfPlane
open scoped Real ModularForm


namespace StatMech.FrontierD

noncomputable section

def etaImaginaryPoint (t : ℝ) (ht : 0 < t) : UpperHalfPlane :=
  ⟨Complex.I * t, by simpa using ht⟩

end
end StatMech.FrontierD
