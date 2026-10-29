/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeBoundaryCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentFiniteMarginal.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def boundaryNonnegativeParityPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior : Finset V) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundaryCurrentPMF G beta J hbeta hJ interior)

noncomputable def boundaryNonnegativeParityRawMass
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (H : Finset (Sym2 V)) : ENNReal := by
  classical
  exact if boundaryParityAllowed G interior H then
    ENNReal.ofReal
      (inhomogeneousParityFiberMass G (fun e => beta * J e) H)
  else 0


end StatMech.FrontierB
