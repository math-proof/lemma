/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

def pathContainsWord {E : Type*} {m k n : ℕ} (p : Fin (k + 1) → E)
    (q : Fin (m + (n + k) + 1) → E) : Prop :=
  ∀ i : Fin (k + 1), q ⟨m + i.val, by omega⟩ = p i

end StatMech.FrontierB
