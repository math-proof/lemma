/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.fullVerticalRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (h : Nat) : Nat :=
  max
    (max
      (((family.radiusLeft h : Int) + family.baseLeft 1 -
        family.baseBottom 1).toNat)
      (((family.radiusRight h : Int) + family.baseRight 1 -
        family.baseBottom 1).toNat))
    (max
      (((family.radiusLeft h : Int) + family.baseTop 1 -
        family.baseLeft 1).toNat)
      (((family.radiusRight h : Int) + family.baseTop 1 -
        family.baseRight 1).toNat))


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.fullHorizontalRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (v : Nat) : Nat :=
  max
    (max
      (((family.radiusBottom v : Int) + family.baseBottom 0 -
        family.baseLeft 0).toNat)
      (((family.radiusTop v : Int) + family.baseTop 0 -
        family.baseLeft 0).toNat))
    (max
      (((family.radiusBottom v : Int) + family.baseRight 0 -
        family.baseBottom 0).toNat)
      (((family.radiusTop v : Int) + family.baseRight 0 -
        family.baseTop 0).toNat))

end StatMech.FK.PeriodicPlanar
