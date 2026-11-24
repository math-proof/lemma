module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

def isingDiagonalDomainPlane (x : freeDomainVertices K) : Prop :=
  x.1 i - x.1 j = c

def isingDiagonalDomainLower (x : freeDomainVertices K) : Prop :=
  x.1 i - x.1 j < c

end Domain
end StatMech.FrontierA
