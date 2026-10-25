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
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

theorem mem_isingDiagonalSymmetricHull_reflect_iff
    (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)
    (x : Site d) :
    x ∈ isingDiagonalSymmetricHull K i j c ↔
      isingDiagonalReflect i j c x ∈ isingDiagonalSymmetricHull K i j c := by
  classical
  constructor
  · intro hx
    rw [isingDiagonalSymmetricHull, Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      left
      rw [← hyx, isingDiagonalReflect_involutive i j hij]
      exact hy
  · intro hx
    have hr := (show isingDiagonalReflect i j c x ∈
        isingDiagonalSymmetricHull K i j c from hx)
    have := (show isingDiagonalReflect i j c
        (isingDiagonalReflect i j c x) ∈
          isingDiagonalSymmetricHull K i j c from
      (by
        rw [isingDiagonalSymmetricHull, Finset.mem_union]
        rw [isingDiagonalSymmetricHull, Finset.mem_union] at hr
        rcases hr with hr | hr
        · exact Or.inr (Finset.mem_image.mpr
            ⟨isingDiagonalReflect i j c x, hr, rfl⟩)
        · obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hr
          left
          rw [← hyr, isingDiagonalReflect_involutive i j hij]
          exact hy))
    rwa [isingDiagonalReflect_involutive i j hij] at this

theorem subset_isingDiagonalSymmetricHull
    (K : Finset (Site d)) (i j : Fin d) (c : Int) :
    K ⊆ isingDiagonalSymmetricHull K i j c := by
  intro x hx
  exact Finset.mem_union_left _ hx


theorem freeDomain_spinProd_diagonalReflect_le
    (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)
    (hK : ∀ x : Site d,
      x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)
    (beta : Real) (hbeta : 0 <= beta)
    (a b : Site d) (ha : a ∈ K) (hb : b ∈ K)
    (hal : a i - a j < c) (hbl : b i - b j < c)
    (hab : a ≠ b)
    (habR : a ≠ isingDiagonalReflect i j c b) :
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K
          {a, isingDiagonalReflect i j c b})) <=
      isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K {a, b})) := by
  let aK : freeDomainVertices K := ⟨a, ha⟩
  let bK : freeDomainVertices K := ⟨b, hb⟩
  let aL : IsingDiagonalDomainLower K i j c := ⟨aK, hal⟩
  let bL : IsingDiagonalDomainLower K i j c := ⟨bK, hbl⟩
  have hfold := isingDiagonalDomain_twoPoint_reflect_le
    K i j hij c hK beta hbeta aL bL
  have hfar : freeDomainSpinSupport K
      {a, isingDiagonalReflect i j c b} =
      {aK, isingDiagonalDomainReflectEquiv K i j hij c hK bK} := by
    ext z
    simp only [freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · left
        apply Subtype.ext
        exact hz
      · right
        apply Subtype.ext
        exact hz
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hnear : freeDomainSpinSupport K {a, b} = {aK, bK} := by
    ext z
    simp only [freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · left
        apply Subtype.ext
        exact hz
      · right
        apply Subtype.ext
        exact hz
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hnearNe : aK ≠ bK := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hfarNe : aK ≠ isingDiagonalDomainReflectEquiv K i j hij c hK bK := by
    intro h
    exact habR (congrArg Subtype.val h)
  rw [hfar, hnear]
  have hfarProd : spinProd
      ({aK, isingDiagonalDomainReflectEquiv K i j hij c hK bK} :
        Finset (freeDomainVertices K)) =
      fun sigma => spin sigma aK *
        spin sigma (isingDiagonalDomainReflectEquiv K i j hij c hK bK) := by
    funext sigma
    rw [spinProd, Finset.prod_pair hfarNe]
  have hnearProd : spinProd ({aK, bK} : Finset (freeDomainVertices K)) =
      fun sigma => spin sigma aK * spin sigma bK := by
    funext sigma
    rw [spinProd, Finset.prod_pair hnearNe]
  rw [hfarProd, hnearProd]
  simpa [aL, bL] using hfold

end StatMech.FrontierA
