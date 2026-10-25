/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

def rectangularPrismSpin {m n h : Nat}
    (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) : Real :=
  spin sigma ⟨x, y, z⟩


def rectangularPrismInternalInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  (∑ x : Fin (m - 1), ∑ y : Fin n, ∑ z : Fin (2 * h + 1),
      rectangularPrismSpin sigma
        ⟨x.val, by omega⟩ y z *
      rectangularPrismSpin sigma
        ⟨x.val + 1, by omega⟩ y z) +
  (∑ x : Fin m, ∑ y : Fin (n - 1), ∑ z : Fin (2 * h + 1),
      rectangularPrismSpin sigma x
        ⟨y.val, by omega⟩ z *
      rectangularPrismSpin sigma x
        ⟨y.val + 1, by omega⟩ z) +
  (∑ x : Fin m, ∑ y : Fin n, ∑ z : Fin (2 * h),
      rectangularPrismSpin sigma x y
        ⟨z.val, by omega⟩ *
      rectangularPrismSpin sigma x y
        ⟨z.val + 1, by omega⟩)


def rectangularPrismBoundaryDegree {m n h : Nat}
    (v : RectangularPrismSite m n h) : Nat :=
  (if v.x.val = 0 then 1 else 0) +
  (if v.x.val + 1 = m then 1 else 0) +
  (if v.y.val = 0 then 1 else 0) +
  (if v.y.val + 1 = n then 1 else 0) +
  (if v.z.val = 0 then 1 else 0) +
  (if v.z.val + 1 = 2 * h + 1 then 1 else 0)


def rectangularPrismPlusBoundaryInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  ∑ v : RectangularPrismSite m n h,
    rectangularPrismBoundaryDegree v * spin sigma v


def rectangularPrismPlusEnergy (J : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  -J * (rectangularPrismInternalInteraction sigma +
    rectangularPrismPlusBoundaryInteraction sigma)


def rectangularPrismInterfaceInteraction {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  if hh : 0 < h then
    ∑ x : Fin m, ∑ y : Fin n,
      rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩
  else 0


def rectangularPrismTwistedEnergy (J : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) : Real :=
  rectangularPrismPlusEnergy J sigma +
    2 * J * rectangularPrismInterfaceInteraction sigma


def rectangularPrismPlusPartition
    (J beta : Real) (m n h : Nat) : Real :=
  Z beta (rectangularPrismPlusEnergy J : RectangularPrismConfig m n h -> Real)


def rectangularPrismTwistedPartition
    (J beta : Real) (m n h : Nat) : Real :=
  Z beta (rectangularPrismTwistedEnergy J : RectangularPrismConfig m n h -> Real)


def rectangularDobrushinFreeEnergy
    (J beta : Real) (m n h : Nat) : Real :=
  Real.log (rectangularPrismPlusPartition J beta m n h) -
    Real.log (rectangularPrismTwistedPartition J beta m n h)


def rectangularDobrushinArray
    (J beta : Real) (m n : Nat) : Real :=
  rectangularDobrushinFreeEnergy J beta m n (max m n)


end
end StatMech.Ising
