/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part3
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


noncomputable def blockInteriorStateEquiv (r m : ℕ) :
    ({x // x ∈ box 1 (r + m)} → Bool) ≃
      (Fin (m + (m + 2 * r) + 1) → Fin 2) :=
  (interiorStateEquiv (r + m)).trans
    (pathCastEquiv (Fin 2) (by omega))

end StatMech.FrontierB
