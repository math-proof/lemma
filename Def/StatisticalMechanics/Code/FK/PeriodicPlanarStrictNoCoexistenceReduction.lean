/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictNoCoexistenceReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC


def StrictDualNoCoexistence
    (primalPercolates dualPercolates : Real → Prop) (q : Real) : Prop :=
  ∀ r ∈ Ioo (0 : Real) 1, ∀ p ∈ Ioo (0 : Real) 1, r < p →
    ¬(primalPercolates r ∧ dualPercolates (dualParam p q))


end StatMech.FK.PeriodicPlanar
