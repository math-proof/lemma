/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


noncomputable def lpMatchingDisconnZero
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i) ∅ g0 g1


noncomputable def lpMatchingDisconnOne
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i ∆ T) ∅ g0 g1


noncomputable def lpMatchingDisconnTwo
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, ∑ j : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i ∆
      lpMatchingSeamSource left right j ∆ T) ∅ g0 g1


noncomputable def lpMatchingDisconnTwoOffDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, ∑ j : I,
    if i = j then 0 else
      sourcePairDisconnSum G beta J
        (lpMatchingSeamSource left right i ∆
          lpMatchingSeamSource left right j ∆ T) ∅ g0 g1


noncomputable def lpMatchingDisconnCenteredGram
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  let dE := sourcePairDisconnSum G beta J ∅ ∅ g0 g1
  ∑ i : I, ∑ j : I, (
    dE * sourcePairDisconnSum G beta J
        (lpMatchingSeamSource left right i ∆
          lpMatchingSeamSource left right j ∆ T) ∅ g0 g1 -
      sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right i) ∅ g0 g1 *
        sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right j ∆ T) ∅ g0 g1 -
      sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right j) ∅ g0 g1 *
        sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right i ∆ T) ∅ g0 g1)


end
end StatMech.Ising
