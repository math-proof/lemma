/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part4
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


def zfk_matchedRect (N : ℕ) : Set (Site 2) :=
  rect (-(N : ℤ)) (N + 1) (-(N : ℤ)) N


def zfk_LeftArmFrom (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (N : ℕ) : Prop :=
  ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.leftSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
    ConnectedWithin 2 omega (zfk_leftSquare N)
      ⟨(a : Site 2), StatMech.RSW.Box.leftSide_subset a.2⟩ ⟨x, hx⟩


def zfk_RightArmFrom (omega : ConfigSpace (Sym2 (Site 2))) (y : Site 2) (N : ℕ) : Prop :=
  ∃ (hy : y ∈ zfk_rightSquare N)
      (b : StatMech.RSW.Box.rightSide
        (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)),
    ConnectedWithin 2 omega (zfk_rightSquare N)
      ⟨y, hy⟩ ⟨(b : Site 2), StatMech.RSW.Box.rightSide_subset b.2⟩


def zfk_ArmPairEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega x).Infinite ∧ (cluster 2 omega y).Infinite ∧
      zfk_LeftArmFrom omega x N ∧ zfk_RightArmFrom omega y N}

def zfk_LeftArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k,
    (cluster 2 omega x).Infinite ∧ zfk_LeftArmFrom omega x N}

def zfk_RightArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ y ∈ zfk_rightCentralBox k,
    (cluster 2 omega y).Infinite ∧ zfk_RightArmFrom omega y N}


def zfk_TopArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.topSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.topSide_subset a.2⟩ ⟨x, hx⟩}

def zfk_CenteredRightArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.rightSide_subset a.2⟩ ⟨x, hx⟩}

def zfk_BottomArmEvent (k N : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ box 2 k, (cluster 2 omega x).Infinite ∧
    ∃ (hx : x ∈ zfk_leftSquare N)
      (a : StatMech.RSW.Box.bottomSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
      ConnectedWithin 2 omega (zfk_leftSquare N)
        ⟨(a : Site 2), StatMech.RSW.Box.bottomSide_subset a.2⟩ ⟨x, hx⟩}

end StatMech.TwoDim
