/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
import Structure.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectUnitWindingOneSource
    (R : FKRectTorus) (q : Real) : FKRectWindingOneSource R q := by
  let x : Fin R.width := ⟨2, R.width_gt_two⟩
  let hx : 2 <= x.val := le_rfl
  let pair :=
    (fkRectRightBandRowOne R 2 x hx,
      fkRectRightBandLastRow R 2 x hx)
  refine
    { leftRight := 1
      cut := 2
      sep := by omega
      left := R.width_gt_two
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := {pair}
      chain_spans := by
        apply fkRectRightBandConnectionChainSpans_of_pair_mem
        simp [pair]
      pair_reachable := ?_
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source R }
  · intro h
    have hdir := congrArg Prod.fst h
    simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir
  · intro xy hxy
    have hxyEq : xy = pair := by simpa using hxy
    subst xy
    exact fkRectRightBand_distinguished_reachable R 2 x hx


noncomputable def fkRectStraightWindingOneSource
    (R : FKRectTorus) (q : Real) (leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width) (hcut : cut < R.width) :
    FKRectWindingOneSource R q := by
  let x : Fin R.width := ⟨cut, hcut⟩
  let hx : cut <= x.val := le_rfl
  let pair :=
    (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx)
  refine
    { leftRight := leftRight
      cut := cut
      sep := hsep
      left := hleft
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := {pair}
      chain_spans := by
        apply fkRectRightBandConnectionChainSpans_of_pair_mem
        simp [pair]
      pair_reachable := ?_
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft }
  · intro h
    have hdir := congrArg Prod.fst h
    simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir
  · intro xy hxy
    have hxyEq : xy = pair := by simpa using hxy
    subst xy
    exact fkRectRightBand_distinguished_reachable R cut x hx


noncomputable def fkRectPathWindingOneSource
    (R : FKRectTorus) (q : Real) (leftRight cut : Nat)
    (hone : 1 <= leftRight) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    (x : Fin R.width) (hx : cut <= x.val) (n : Nat)
    (v : Fin (n + 1) ->
      FKRectRightStripBandVertex R cut 1 (R.height - 1))
    (hfirst : v 0 = fkRectRightBandRowOne R cut x hx)
    (hlast : v (Fin.last n) = fkRectRightBandLastRow R cut x hx)
    (hreaches : ∀ xy ∈ connectionPathPairs n v,
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
          xy.1 xy.2) :
    FKRectWindingOneSource R q := by
  refine
    { leftRight := leftRight
      cut := cut
      sep := hsep
      left := hleft
      gap := fkRectUnitLeftBarrierGap R
      gap_mem := fkRectUnitLeftBarrierGap_mem R
      x := x
      x_right := hx
      chosen := ?_
      pairs := connectionPathPairs n v
      chain_spans :=
        fkRectRightBandConnectionChainSpans_connectionPathPairs
          R cut x hx n v hfirst hlast
      pair_reachable := hreaches
      barrierConfiguration := fkRectUnitLeftBarrierConfiguration R
      barrier_mem := fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
        R leftRight hone hleft }
  intro h
  have hdir := congrArg Prod.fst h
  simp [fkRectVerticalSeamEdgeAt, fkRectUnitLeftBarrierGap] at hdir

noncomputable def FKRectWindingOneSource.connectionProduct
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q) : Real :=
  ∏ xy ∈ source.pairs,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R source.cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2

noncomputable def FKRectWindingOneSource.barrierMass
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q) : Real :=
  fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R source.leftRight source.gap)

end
end StatMech.FrontierD
