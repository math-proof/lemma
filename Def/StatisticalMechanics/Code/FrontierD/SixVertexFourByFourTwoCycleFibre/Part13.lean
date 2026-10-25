/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedCoordinateRowZero
    (firstSeam secondSeam : Fin 4) : Fin 16 :=
  ![![1, 0, 2, 3], ![5, 4, 6, 7],
    ![13, 12, 14, 15], ![9, 8, 10, 11]] firstSeam secondSeam

def sixVertexFourByFourAuditedMiddleA (secondSeam : Fin 4) : Fin 16 :=
  ![2, 3, 1, 0] secondSeam

def sixVertexFourByFourAuditedMiddleB (firstSeam : Fin 4) : Fin 16 :=
  ![10, 8, 4, 6] firstSeam

def sixVertexFourByFourAuditedMiddleBNext (firstSeam : Fin 4) : Fin 16 :=
  ![11, 9, 5, 7] firstSeam

def sixVertexFourByFourAuditedMiddleC (secondSeam : Fin 4) : Fin 16 :=
  ![14, 15, 13, 12] secondSeam

def sixVertexFourByFourAuditedMiddlePair
    (firstSeam secondSeam : Fin 4) : Fin 8 -> Fin 16 × Fin 16 := ![
  (sixVertexFourByFourAuditedMiddleA secondSeam,
    sixVertexFourByFourAuditedMiddleB firstSeam),
  (sixVertexFourByFourAuditedMiddleA secondSeam,
    sixVertexFourByFourAuditedMiddleBNext firstSeam),
  (sixVertexFourByFourAuditedMiddleB firstSeam,
    sixVertexFourByFourAuditedMiddleA secondSeam),
  (sixVertexFourByFourAuditedMiddleB firstSeam,
    sixVertexFourByFourAuditedMiddleC secondSeam),
  (sixVertexFourByFourAuditedMiddleBNext firstSeam,
    sixVertexFourByFourAuditedMiddleA secondSeam),
  (sixVertexFourByFourAuditedMiddleBNext firstSeam,
    sixVertexFourByFourAuditedMiddleC secondSeam),
  (sixVertexFourByFourAuditedMiddleC secondSeam,
    sixVertexFourByFourAuditedMiddleB firstSeam),
  (sixVertexFourByFourAuditedMiddleC secondSeam,
    sixVertexFourByFourAuditedMiddleBNext firstSeam)
]

def sixVertexFourByFourAuditedCoordinateParameters
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedHorizontalParameters :=
  let middle := sixVertexFourByFourAuditedMiddlePair
    c.firstSeam c.secondSeam c.middle
  (sixVertexFourByFourAuditedCoordinateRowZero c.firstSeam c.secondSeam,
    middle.1, middle.2, c.last)

def sixVertexFourByFourAuditedCoordinateSourcePair
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  (sixVertexFourByFourAuditedParamSourceFirst
      (sixVertexFourByFourAuditedCoordinateParameters c) c.firstSeam,
    sixVertexFourByFourAuditedParamSourceSecond
      (sixVertexFourByFourAuditedCoordinateParameters c) c.secondSeam)

def SixVertexFourByFourAuditedCoordinateSourcePairValid
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
    (sixVertexFourByFourAuditedCoordinateSourcePair c).1.IceRule /\
      (sixVertexFourByFourAuditedCoordinateSourcePair c).2.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedCoordinateSourcePair c).1
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedCoordinateSourcePair c).2
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3

def SixVertexFourByFourAuditedCoordinateRowsInvariant
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y) = 1) /\
    (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y) = 3) /\
    sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorOneSeamMask c.firstSeam) /\
    sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorThreeSeamMask c.secondSeam)

end
end StatMech.FrontierD
