/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


def fkMedialVerticalSeamDart (T : EvenTorus) (i : Fin T.width) :
    FKMedialDart T :=
  ((i, svFinLast T.height_pos), .north)


def fkOrientedVerticalSeamSign (T : EvenTorus)
    (arrows : SixVertexArrows T) (i : Fin T.width) : Int :=
  if arrows.vertical (i, svFinLast T.height_pos) then 1 else -1


def fkMedialCanonicalVerticalSeamSign (T : EvenTorus)
    (i : Fin T.width) : Int :=
  if fkMedialCheckerColor (fkMedialVerticalSeamDart T i) then -1 else 1


def fkMedialLoopCanonicalVerticalFlux
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ i : Fin T.width,
    if (fkMedialLoopGraph T pairing).connectedComponentMk
          (fkMedialVerticalSeamDart T i) = C then
      fkMedialCanonicalVerticalSeamSign T i
    else 0


def fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) : Nat :=
  ∑ C : FKMedialLoop T pairing,
    (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs


def fkMedialVerticallyWindingComponents
    (pairing : FKMedialLoopPairing T) : Finset (FKMedialLoop T pairing) := by
  classical
  exact Finset.univ.filter fun C =>
    fkMedialLoopCanonicalVerticalFlux pairing C ≠ 0


end
end StatMech.FrontierD
