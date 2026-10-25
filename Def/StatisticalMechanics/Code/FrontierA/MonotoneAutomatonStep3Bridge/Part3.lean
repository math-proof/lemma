/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part3
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def PairHighClusterAbsorption (omega : PairSiteConfig d) : Prop :=
  ∀ x : Site d, (pairHighCluster omega x).Infinite →
    (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty


end StatMech.FrontierA
