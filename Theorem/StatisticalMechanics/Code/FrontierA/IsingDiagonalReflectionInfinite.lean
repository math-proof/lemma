/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}


theorem freeDomain_spinProd_le_freeState
    (K : Finset (Site d)) (beta : Real) (hbeta : 0 <= beta)
    (A : Finset (Site d)) (hA : A ⊆ K) :
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) <=
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  obtain ⟨N, hKN⟩ := Lattice.finite_subset_box
    (↑K : Set (Site d)) K.finite_toSet
  have hKbox : K ⊆ boxFinset d N := by
    intro x hx
    rw [mem_boxFinset]
    exact hKN hx
  have hlim := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with n hn
  have hKboxn : K ⊆ boxFinset d n := by
    intro x hx
    have hxN := hKbox hx
    rw [mem_boxFinset] at hxN ⊢
    exact box_mono d hn hxN
  rw [integral_freeMeasure_spinProd_eq_freeDomain d n beta A
    (hA.trans hKboxn)]
  exact freeDomain_spinProd_mono hKboxn beta hbeta A hA


theorem integral_freeState_spinProd_diagonalReflect_le
    (i j : Fin d) (hij : i ≠ j) (c : Int)
    (beta : Real) (hbeta : 0 <= beta)
    (a b : Site d)
    (hal : a i - a j < c) (hbl : b i - b j < c)
    (hab : a ≠ b)
    (habR : a ≠ isingDiagonalReflect i j c b) :
    (∫ omega, spinProd
        ({a, isingDiagonalReflect i j c b} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) <=
      ∫ omega, spinProd ({a, b} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  let Rb := isingDiagonalReflect i j c b
  let S : Finset (Site d) := {a, b, Rb}
  obtain ⟨N, hSN⟩ := Lattice.finite_subset_box
    (↑S : Set (Site d)) S.finite_toSet
  let Afar : Finset (Site d) := {a, Rb}
  let Anear : Finset (Site d) := {a, b}
  have hlim : Tendsto
      (fun n => ∫ omega, spinProd Afar omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd Afar omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta Afar
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with n hn
  let B := boxFinset d n
  let K := isingDiagonalSymmetricHull B i j c
  have hSbox : S ⊆ B := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d hn (hSN hx)
  have haB : a ∈ B := hSbox (by simp [S])
  have hbB : b ∈ B := hSbox (by simp [S])
  have hRbB : Rb ∈ B := hSbox (by simp [S])
  have hBK : B ⊆ K := subset_isingDiagonalSymmetricHull B i j c
  have haK : a ∈ K := hBK haB
  have hbK : b ∈ K := hBK hbB
  have hAfarB : Afar ⊆ B := by
    intro x hx
    simp only [Afar, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haB
    · exact hRbB
  have hAnearK : Anear ⊆ K := by
    intro x hx
    simp only [Anear, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haK
    · exact hbK
  have hK : ∀ x : Site d,
      x ∈ K ↔ isingDiagonalReflect i j c x ∈ K :=
    mem_isingDiagonalSymmetricHull_reflect_iff B i j hij c
  calc
    (∫ omega, spinProd Afar omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
      isingExpectation (freeDomainGraph B) beta 0
        (spinProd (freeDomainSpinSupport B Afar)) := by
          exact integral_freeMeasure_spinProd_eq_freeDomain
            d n beta Afar hAfarB
    _ <= isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K Afar)) :=
      freeDomain_spinProd_mono hBK beta hbeta Afar hAfarB
    _ <= isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K Anear)) := by
      simpa [Afar, Anear, Rb] using
        freeDomain_spinProd_diagonalReflect_le K i j hij c hK
          beta hbeta a b haK hbK hal hbl hab habR
    _ <= ∫ omega, spinProd Anear omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
      freeDomain_spinProd_le_freeState K beta hbeta Anear hAnearK


theorem currentContinuityFreeTwoPoint_diagonalReflect_le
    (i j : Fin d) (hij : i ≠ j) (c : Int)
    (beta : Real) (hbeta : 0 <= beta)
    (a b : Site d)
    (hal : a i - a j < c) (hbl : b i - b j < c)
    (hab : a ≠ b)
    (habR : a ≠ isingDiagonalReflect i j c b) :
    currentContinuityFreeTwoPoint d beta a
        (isingDiagonalReflect i j c b) <=
      currentContinuityFreeTwoPoint d beta a b := by
  exact integral_freeState_spinProd_diagonalReflect_le
    i j hij c beta hbeta a b hal hbl hab habR


end StatMech.FrontierA
