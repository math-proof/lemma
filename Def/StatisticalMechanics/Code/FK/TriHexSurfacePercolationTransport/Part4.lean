/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part3
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

noncomputable def triangularWiredBoundaryArmProbability
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : Nat) : Real :=
  (triangular.wiredBufferedInfiniteVolume hp hp1 hq :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.bufferedCylinder n
        (triangular.bufferedRootBoundaryEvent n))


noncomputable def hexagonalWiredBoundaryArmProbability
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (n : Nat) : Real :=
  (hexagonal.wiredBufferedInfiniteVolume
      (BeffaraDC.dualParam_pos hp hp1 hq)
      (BeffaraDC.dualParam_lt_one hp hp1 hq) hq :
    Measure (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.bufferedCylinder n
        (hexagonal.bufferedRootBoundaryEvent n))


def TriHexTorusBufferedReachApproximation
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  Tendsto
      (fun n => triangularTorusRadialReachProbability p q n -
        triangularWiredBoundaryArmProbability hp hp1 hq n)
      atTop (nhds 0) ∧
    Tendsto
      (fun n => hexagonalTorusRadialReachProbability p q n -
        hexagonalWiredBoundaryArmProbability hp hp1 hq n)
      atTop (nhds 0)


end
end StatMech.FK.PeriodicPlanar
