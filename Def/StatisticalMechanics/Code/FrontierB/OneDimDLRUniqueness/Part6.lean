/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part4
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


noncomputable def fvBlockStateProb (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (beta h : ℝ) (p : Fin (2 * r + 1) → Fin 2) : ℝ :=
  ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
    if glue eta tau ∈ blockStateEvent r p then
      fvProb eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0

end StatMech.FrontierB
