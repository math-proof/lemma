/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part2


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

def isingCoordinateDomainSplitEquiv :
    (ConfigSpace (IsingCoordinateDomainPlane K i m) ×
      (ConfigSpace (IsingCoordinateDomainLower K i m) ×
        ConfigSpace (IsingCoordinateDomainLower K i m))) ≃
      ConfigSpace (freeDomainVertices K) where
  toFun p := isingCoordinateDomainGlue K i m hK p.1 p.2.1 p.2.2
  invFun := isingCoordinateDomainSplit K i m hK
  left_inv p := by rcases p with ⟨b, l, u⟩; simp
  right_inv := isingCoordinateDomainGlue_split K i m hK

end
end StatMech.FrontierA
