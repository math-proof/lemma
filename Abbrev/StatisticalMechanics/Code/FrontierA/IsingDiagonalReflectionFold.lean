/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Instance.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

abbrev IsingDiagonalDomainPlane :=
  {x : freeDomainVertices K // isingDiagonalDomainPlane K i j c x}

abbrev IsingDiagonalDomainLower :=
  {x : freeDomainVertices K // isingDiagonalDomainLower K i j c x}

end Domain
end StatMech.FrontierA
