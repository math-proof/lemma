/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Abbrev.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def pairSiteConfig (eta zeta : ConfigSpace (Site d)) : PairSiteConfig d
  | Sum.inl x => eta x
  | Sum.inr x => zeta x


def pairSiteLeft (omega : PairSiteConfig d) : ConfigSpace (Site d) :=
  fun x => omega (Sum.inl x)


def pairSiteRight (omega : PairSiteConfig d) : ConfigSpace (Site d) :=
  fun x => omega (Sum.inr x)

end StatMech.FrontierA
