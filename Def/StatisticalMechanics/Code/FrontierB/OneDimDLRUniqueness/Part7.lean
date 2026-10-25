/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part5
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


noncomputable def blockStateLimit (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) : ℝ :=
  isingTransferProjectorPlus beta (beta * h) (p (Fin.last (2 * r))) (p 0) *
    fixedWordProduct (isingTransferReal beta (beta * h)) p *
      (isingTransferEigenPlus beta (beta * h))⁻¹ ^ (2 * r)

end StatMech.FrontierB
