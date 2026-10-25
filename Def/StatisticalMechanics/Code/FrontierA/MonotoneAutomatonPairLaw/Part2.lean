/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def interpolatedHighPair (T : MonotoneAutomaton d)
    (q : FieldTriple d) : PairSiteConfig d :=
  pairSiteConfig (interpolatedSite T q) (T q.2.2)

end StatMech.FrontierA
