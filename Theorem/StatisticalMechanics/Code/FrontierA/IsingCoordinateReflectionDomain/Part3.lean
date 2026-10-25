/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part4


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

theorem isingCoordinateDomainGlue_reflect
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingCfgEquiv (isingCoordinateDomainReflectEquiv K i m hK)
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      isingCoordinateDomainGlue K i m hK boundary upper lower := by
  funext x
  by_cases hp : isingCoordinateDomainPlane K i m x
  · have hfixed := isingCoordinateDomainReflect_fixed K i m hK hp
    simp [isingCfgEquiv, isingCoordinateDomainGlue, hp, hfixed]
  · by_cases hl : isingCoordinateDomainLower K i m x
    · have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      have hlR := isingCoordinateDomainReflect_not_lower_of_lower
        K i m hK hl
      have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x) = x :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x
      simp [isingCfgEquiv, isingCoordinateDomainGlue,
        hp, hl, hpR, hlR, hRR]
    · have hlR := isingCoordinateDomainReflect_lower_of_upper
        K i m hK hp hl
      have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      simp [isingCfgEquiv, isingCoordinateDomainGlue, hp, hl, hpR, hlR]

end
end StatMech.FrontierA
