/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part3


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

@[simp] theorem isingCoordinateDomainSplit_glue
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingCoordinateDomainSplit K i m hK
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue, x.2]
  · apply Prod.ext
    · funext x
      have hp : ¬ isingCoordinateDomainPlane K i m x.1 := by
        intro hplane
        have hl : 2 * x.1.1 i < m := x.2
        have heq : 2 * x.1.1 i = m := hplane
        omega
      simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue, hp, x.2]
    · funext x
      have hp : ¬ isingCoordinateDomainPlane K i m x.1 := by
        intro hplane
        have hl : 2 * x.1.1 i < m := x.2
        have heq : 2 * x.1.1 i = m := hplane
        omega
      have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      have hlR := isingCoordinateDomainReflect_not_lower_of_lower
        K i m hK x.2
      have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x.1) = x.1 :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x.1
      simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue,
        hpR, hlR, hRR]

@[simp] theorem isingCoordinateDomainGlue_split
    (sigma : ConfigSpace (freeDomainVertices K)) :
    isingCoordinateDomainGlue K i m hK
        (isingCoordinateDomainSplit K i m hK sigma).1
        (isingCoordinateDomainSplit K i m hK sigma).2.1
        (isingCoordinateDomainSplit K i m hK sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingCoordinateDomainPlane K i m x
  · simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp]
  · by_cases hl : isingCoordinateDomainLower K i m x
    · simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp, hl]
    · have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x) = x :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x
      simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp, hl, hRR]

end
end StatMech.FrontierA
