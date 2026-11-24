module
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
public import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
public import Structure.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


noncomputable def certificate
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) : RGCertificate M :=
  P.closedBallRG.certificate scale M

end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
