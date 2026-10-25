/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Instance.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

def wordHeadSplitEquiv (E : Type*) (m k n : ℕ) :
    E × ((Fin m → E) × (Fin (n + k + 1) → E)) ≃
      (Fin (m + (n + k + 1) + 1) → E) :=
  splitPathEquiv E m (n + k + 1)

end StatMech.FrontierB
