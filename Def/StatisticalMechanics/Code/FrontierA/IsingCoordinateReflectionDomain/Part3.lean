/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

def isingCoordinateDomainGlue
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    ConfigSpace (freeDomainVertices K) :=
  fun x => if hp : isingCoordinateDomainPlane K i m x then
      boundary ⟨x, hp⟩
    else if hl : isingCoordinateDomainLower K i m x then
      lower ⟨x, hl⟩
    else upper ⟨isingCoordinateDomainReflectEquiv K i m hK x,
      isingCoordinateDomainReflect_lower_of_upper K i m hK hp hl⟩

def isingCoordinateDomainSplit
    (sigma : ConfigSpace (freeDomainVertices K)) :
    ConfigSpace (IsingCoordinateDomainPlane K i m) ×
      (ConfigSpace (IsingCoordinateDomainLower K i m) ×
        ConfigSpace (IsingCoordinateDomainLower K i m)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1,
      fun x => sigma (isingCoordinateDomainReflectEquiv K i m hK x.1)))

end
end StatMech.FrontierA
