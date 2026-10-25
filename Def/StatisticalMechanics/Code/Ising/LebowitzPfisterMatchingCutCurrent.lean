/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostVarianceSector
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


def lpMatchingSeamSource (left right : I -> W) (i : I) : Finset W :=
  ({left i} : Finset W) ∆ {right i}


def lpMatchingGhostSource (g0 g1 : W) : Finset W :=
  ({g0} : Finset W) ∆ {g1}

noncomputable def lpMatchingCurrentZ
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real) : Real :=
  currentSum G beta J ∅

noncomputable def lpMatchingCurrentA
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) : Real :=
  ∑ i : I, currentSum G beta J (lpMatchingSeamSource left right i)

noncomputable def lpMatchingCurrentB
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)

noncomputable def lpMatchingCurrentC
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real) (g0 g1 : W) : Real :=
  currentSum G beta J (lpMatchingGhostSource g0 g1)

noncomputable def lpMatchingCurrentD
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) : Real :=
  ∑ i : I, ∑ j : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)

noncomputable def lpMatchingCurrentE
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, ∑ j : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆
      lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)


def lpMatchingCurrentSkewPolynomial (A B C D E Z : Real) : Real :=
  (Z ^ 2 - C ^ 2) *
      (((E * Z - D * C) * Z) - 2 * A * (B * Z - A * C)) +
    2 * C * (B * Z - A * C) ^ 2


end
end StatMech.Ising
