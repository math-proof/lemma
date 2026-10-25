/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part2


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

@[simp] theorem isingCoordinateDomainReflectEquiv_val
    (x : freeDomainVertices K) :
    (isingCoordinateDomainReflectEquiv K i m hK x).1 =
      isingCoordinateReflect i m x.1 := rfl

theorem isingCoordinateDomainReflectEquiv_adj
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      (freeDomainGraph K).Adj
        (isingCoordinateDomainReflectEquiv K i m hK x)
        (isingCoordinateDomainReflectEquiv K i m hK y) :=
  hypercubicLattice_adj_coordinateReflect i m x.1 y.1

theorem isingCoordinateDomainReflect_fixed
    {x : freeDomainVertices K}
    (hx : isingCoordinateDomainPlane K i m x) :
    isingCoordinateDomainReflectEquiv K i m hK x = x := by
  apply Subtype.ext
  exact isingCoordinateReflect_fixed i m x.1 hx

theorem isingCoordinateDomainReflect_lower_of_upper
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x)
    (hl : ¬ isingCoordinateDomainLower K i m x) :
    isingCoordinateDomainLower K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_lower_of_upper i m x.1 hp hl

theorem isingCoordinateDomainReflect_not_plane
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x) :
    ¬ isingCoordinateDomainPlane K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_not_plane i m x.1 hp

theorem isingCoordinateDomainReflect_not_lower_of_lower
    {x : freeDomainVertices K}
    (hl : isingCoordinateDomainLower K i m x) :
    ¬ isingCoordinateDomainLower K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_not_lower_of_lower i m x.1 hl

end
end StatMech.FrontierA
