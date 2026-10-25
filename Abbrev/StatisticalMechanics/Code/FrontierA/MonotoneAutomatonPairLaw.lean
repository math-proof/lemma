/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


abbrev PairSiteConfig (d : ℕ) := ConfigSpace (Site d ⊕ Site d)


end StatMech.FrontierA
