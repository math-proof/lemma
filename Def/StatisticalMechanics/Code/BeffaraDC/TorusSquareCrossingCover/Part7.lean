/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part6
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def torusPlanarSquareFaceDualHom
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L) :
    (openSubgraph 2
      (fci_faceDualConfig (torusPlanarPullback L omega))).induce
        (rect 0 (n : ℤ) 0 (n : ℤ)) →g
      (FK.openSub (onsTorusGraph L)
        (torusAmbientConfigExtend L
          (torusAmbientSwapConfig L
            (torusCellDualAmbientConfig L omega)))).induce
        (torusSquareVertexSet L n) where
  toFun x := ⟨torusReduceSwapSite L x,
    torusReduceSwapSite_mem_square L n hnL x.2⟩
  map_rel' := by
    intro x y hxy
    exact (torusPlanarFaceDualHom L omega).map_rel hxy


end StatMech.BeffaraDC
