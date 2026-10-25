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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

def isingDiagonalDomainSplitEquiv :
    (ConfigSpace (IsingDiagonalDomainPlane K i j c) ×
      (ConfigSpace (IsingDiagonalDomainLower K i j c) ×
        ConfigSpace (IsingDiagonalDomainLower K i j c))) ≃
      ConfigSpace (freeDomainVertices K) where
  toFun p := isingDiagonalDomainGlue K i j hij c hK p.1 p.2.1 p.2.2
  invFun := isingDiagonalDomainSplit K i j hij c hK
  left_inv p := by rcases p with ⟨b, l, u⟩; simp
  right_inv := isingDiagonalDomainGlue_split K i j hij c hK

end Domain
end StatMech.FrontierA
