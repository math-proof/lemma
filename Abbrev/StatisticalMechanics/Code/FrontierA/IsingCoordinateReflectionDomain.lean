module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
public import Instance.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

abbrev IsingCoordinateDomainPlane :=
  {x : freeDomainVertices K // isingCoordinateDomainPlane K i m x}

abbrev IsingCoordinateDomainLower :=
  {x : freeDomainVertices K // isingCoordinateDomainLower K i m x}

end
end StatMech.FrontierA
