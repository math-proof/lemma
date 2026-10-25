/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingDrivingReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.FKIsingInterfaceConvergenceReduction
import Theorem.StatisticalMechanics.Code.SLE.CanonicalBrownianLaw
import Theorem.StatisticalMechanics.Code.SLE.CanonicalBrownianSLE
open Filter MeasureTheory


namespace StatMech.SLE

noncomputable def fkIsingObservableJet (t W u : Real) : Real :=
  1 + W / 2 * u + (3 * W ^ 2 - 16 * t) / 8 * u ^ 2


end StatMech.SLE
