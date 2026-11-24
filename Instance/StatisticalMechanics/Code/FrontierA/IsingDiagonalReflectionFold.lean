module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold
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

instance (x : freeDomainVertices K) :
    Decidable (isingDiagonalDomainPlane K i j c x) := by
  unfold isingDiagonalDomainPlane
  infer_instance

instance (x : freeDomainVertices K) :
    Decidable (isingDiagonalDomainLower K i j c x) := by
  unfold isingDiagonalDomainLower
  infer_instance

end Domain
end StatMech.FrontierA
