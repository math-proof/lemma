/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

def isingCoordinateDomainReflectEquiv :
    freeDomainVertices K ≃ freeDomainVertices K where
  toFun x := ⟨isingCoordinateReflect i m x.1, (hK x.1).1 x.2⟩
  invFun x := ⟨isingCoordinateReflect i m x.1, (hK x.1).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact isingCoordinateReflect_involutive i m x.1
  right_inv x := by
    apply Subtype.ext
    exact isingCoordinateReflect_involutive i m x.1

end
end StatMech.FrontierA
