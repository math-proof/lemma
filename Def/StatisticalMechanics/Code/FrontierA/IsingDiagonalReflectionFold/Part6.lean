module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part4
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

noncomputable def isingDiagonalSymmetricHull
    (K : Finset (Site d)) (i j : Fin d) (c : Int) : Finset (Site d) :=
  K ∪ K.image (isingDiagonalReflect i j c)

end StatMech.FrontierA
