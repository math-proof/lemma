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
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

@[simp] theorem isingDiagonalDomainReflectEquiv_val
    (x : freeDomainVertices K) :
    (isingDiagonalDomainReflectEquiv K i j hij c hK x).1 =
      isingDiagonalReflect i j c x.1 := rfl

theorem isingDiagonalDomainReflectEquiv_adj
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      (freeDomainGraph K).Adj
        (isingDiagonalDomainReflectEquiv K i j hij c hK x)
        (isingDiagonalDomainReflectEquiv K i j hij c hK y) := by
  exact hypercubicLattice_adj_diagonalReflect i j hij c x.1 y.1

theorem isingDiagonalDomainReflect_fixed
    {x : freeDomainVertices K}
    (hx : isingDiagonalDomainPlane K i j c x) :
    isingDiagonalDomainReflectEquiv K i j hij c hK x = x := by
  apply Subtype.ext
  exact isingDiagonalReflect_fixed i j hij c x.1 hx

theorem isingDiagonalDomainReflect_lower_of_upper
    {x : freeDomainVertices K}
    (hp : ¬ isingDiagonalDomainPlane K i j c x)
    (hl : ¬ isingDiagonalDomainLower K i j c x) :
    isingDiagonalDomainLower K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  unfold isingDiagonalDomainPlane at hp
  unfold isingDiagonalDomainLower at hl ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij]
  omega

theorem isingDiagonalDomainReflect_not_plane
    {x : freeDomainVertices K}
    (hp : ¬ isingDiagonalDomainPlane K i j c x) :
    ¬ isingDiagonalDomainPlane K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  intro hr
  apply hp
  unfold isingDiagonalDomainPlane at hr ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij] at hr
  omega

theorem isingDiagonalDomainReflect_not_lower_of_lower
    {x : freeDomainVertices K}
    (hl : isingDiagonalDomainLower K i j c x) :
    ¬ isingDiagonalDomainLower K i j c
      (isingDiagonalDomainReflectEquiv K i j hij c hK x) := by
  unfold isingDiagonalDomainLower at hl ⊢
  rw [isingDiagonalDomainReflectEquiv_val,
    isingDiagonalReflect_difference i j hij]
  omega


end Domain
end StatMech.FrontierA
