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
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

@[simp] theorem isingDiagonalDomainSplit_glue
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainSplit K i j hij c hK
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, x.2]
  · apply Prod.ext
    · funext x
      have hp : ¬ isingDiagonalDomainPlane K i j c x.1 := by
        exact ne_of_lt x.2
      simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, hp, x.2]
    · funext x
      have hp : ¬ isingDiagonalDomainPlane K i j c x.1 := by
        exact ne_of_lt x.2
      have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      have hlR := isingDiagonalDomainReflect_not_lower_of_lower
        K i j hij c hK x.2
      have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x.1) = x.1 :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x.1
      simp [isingDiagonalDomainSplit, isingDiagonalDomainGlue, hpR, hlR, hRR]

@[simp] theorem isingDiagonalDomainGlue_split
    (sigma : ConfigSpace (freeDomainVertices K)) :
    isingDiagonalDomainGlue K i j hij c hK
        (isingDiagonalDomainSplit K i j hij c hK sigma).1
        (isingDiagonalDomainSplit K i j hij c hK sigma).2.1
        (isingDiagonalDomainSplit K i j hij c hK sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · have hfixed := isingDiagonalDomainReflect_fixed K i j hij c hK hp
    simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hfixed]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hl]
    · have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x) = x :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x
      simp [isingDiagonalDomainGlue, isingDiagonalDomainSplit, hp, hl, hRR]

end Domain
end StatMech.FrontierA
