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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

def isingDiagonalDomainGlue
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    ConfigSpace (freeDomainVertices K) :=
  fun x => if hp : isingDiagonalDomainPlane K i j c x then
      boundary ⟨x, hp⟩
    else if hl : isingDiagonalDomainLower K i j c x then
      lower ⟨x, hl⟩
    else upper ⟨isingDiagonalDomainReflectEquiv K i j hij c hK x,
      isingDiagonalDomainReflect_lower_of_upper K i j hij c hK hp hl⟩

def isingDiagonalDomainSplit
    (sigma : ConfigSpace (freeDomainVertices K)) :
    ConfigSpace (IsingDiagonalDomainPlane K i j c) ×
      (ConfigSpace (IsingDiagonalDomainLower K i j c) ×
        ConfigSpace (IsingDiagonalDomainLower K i j c)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1,
      fun x => sigma (isingDiagonalDomainReflectEquiv K i j hij c hK x.1)))

end Domain
end StatMech.FrontierA
