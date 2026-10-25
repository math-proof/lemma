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
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

theorem isingDiagonalDomainWeight_factor
    (beta : Real)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower *
        isingDiagonalDomainHalfWeight K i j hij c hK beta boundary upper := by
  unfold isingWeight isingDiagonalDomainHalfWeight
  rw [← Real.exp_add]
  congr 1
  have hmid := isingDiagonalDomain_hamiltonian_midpoint
    K i j hij c hK boundary lower upper
  linear_combination (-beta / 2) * hmid

theorem isingDiagonalDomainHalfWeight_pos
    (beta : Real)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    0 < isingDiagonalDomainHalfWeight K i j hij c hK beta boundary lower :=
  Real.exp_pos _

theorem isingDiagonalDomainGlue_self_sup
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainGlue K i j hij c hK boundary (lower ⊔ upper) (lower ⊔ upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary lower lower ⊔
        isingDiagonalDomainGlue K i j hij c hK boundary upper upper := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · simp [isingDiagonalDomainGlue, hp]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, hp, hl]
    · simp [isingDiagonalDomainGlue, hp, hl]

theorem isingDiagonalDomainGlue_self_inf
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingDiagonalDomainGlue K i j hij c hK boundary (lower ⊓ upper) (lower ⊓ upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary lower lower ⊓
        isingDiagonalDomainGlue K i j hij c hK boundary upper upper := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · simp [isingDiagonalDomainGlue, hp]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · simp [isingDiagonalDomainGlue, hp, hl]
    · simp [isingDiagonalDomainGlue, hp, hl]

theorem isingDiagonalDomainHalfWeight_fkg
    (beta : Real) (hbeta : 0 <= beta)
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c)) :
    FKGLatticeCondition
      (isingDiagonalDomainHalfWeight K i j hij c hK beta boundary) := by
  intro lower upper
  unfold isingDiagonalDomainHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsub := ifk_hamiltonian_submodular (freeDomainGraph K) 0
    (isingDiagonalDomainGlue K i j hij c hK boundary lower lower)
    (isingDiagonalDomainGlue K i j hij c hK boundary upper upper)
  rw [← isingDiagonalDomainGlue_self_sup K i j hij c hK,
    ← isingDiagonalDomainGlue_self_inf K i j hij c hK] at hsub
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hsub)]


theorem isingDiagonalDomain_twoPoint_reflect_le
    (beta : Real) (hbeta : 0 <= beta)
    (x y : IsingDiagonalDomainLower K i j c) :
    isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma x.1 * spin sigma
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1)) <=
      isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma x.1 * spin sigma y.1) := by
  let w := isingDiagonalDomainHalfWeight K i j hij c hK beta
  let fx : ConfigSpace (IsingDiagonalDomainLower K i j c) -> Real :=
    fun sigma => spin sigma x
  let gy : ConfigSpace (IsingDiagonalDomainLower K i j c) -> Real :=
    fun sigma => spin sigma y
  have hfold := markovReflectionFold_sum_le w
    (fun b sigma => isingDiagonalDomainHalfWeight_pos
      K i j hij c hK beta b sigma)
    (fun b => isingDiagonalDomainHalfWeight_fkg
      K i j hij c hK beta hbeta b)
    fx gy
    (fun _ _ h => ifk_spin_mono h x)
    (fun _ _ h => ifk_spin_mono h y)
  have hcross :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) =
        ∑ b, ∑ l, ∑ u, (w b l * w b u) * (fx l * gy u) := by
    rw [← (isingDiagonalDomainSplitEquiv K i j hij c hK).bijective.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro u _
    change isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK b l u) *
          (spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 *
            spin (isingDiagonalDomainGlue K i j hij c hK b l u)
              (isingDiagonalDomainReflectEquiv K i j hij c hK y.1)) = _
    rw [isingDiagonalDomainWeight_factor]
    have hxp : ¬ isingDiagonalDomainPlane K i j c x.1 := ne_of_lt x.2
    have hyp : ¬ isingDiagonalDomainPlane K i j c y.1 := ne_of_lt y.2
    have hypR := isingDiagonalDomainReflect_not_plane K i j hij c hK hyp
    have hylR := isingDiagonalDomainReflect_not_lower_of_lower
      K i j hij c hK y.2
    have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
        (isingDiagonalDomainReflectEquiv K i j hij c hK y.1) = y.1 :=
      (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv y.1
    have hxspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 =
        spin l x := by
      simp [spin, isingDiagonalDomainGlue, hxp, x.2]
    have hyspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u)
        (isingDiagonalDomainReflectEquiv K i j hij c hK y.1) = spin u y := by
      simp [spin, isingDiagonalDomainGlue, hypR, hylR, hRR]
    rw [hxspin, hyspin]
  have hsame :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma y.1)) =
        ∑ b, ∑ l, ∑ u, (w b l * w b u) * (fx l * gy l) := by
    rw [← (isingDiagonalDomainSplitEquiv K i j hij c hK).bijective.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro u _
    change isingWeight (freeDomainGraph K) beta 0
        (isingDiagonalDomainGlue K i j hij c hK b l u) *
          (spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 *
            spin (isingDiagonalDomainGlue K i j hij c hK b l u) y.1) = _
    rw [isingDiagonalDomainWeight_factor]
    have hxp : ¬ isingDiagonalDomainPlane K i j c x.1 := ne_of_lt x.2
    have hyp : ¬ isingDiagonalDomainPlane K i j c y.1 := ne_of_lt y.2
    have hxspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) x.1 =
        spin l x := by
      simp [spin, isingDiagonalDomainGlue, hxp, x.2]
    have hyspin : spin (isingDiagonalDomainGlue K i j hij c hK b l u) y.1 =
        spin l y := by
      simp [spin, isingDiagonalDomainGlue, hyp, y.2]
    rw [hxspin, hyspin]
  unfold isingExpectation isingProb
  let Z := isingZ (freeDomainGraph K) beta 0
  have hZ : 0 <= Z := (isingZ_pos (freeDomainGraph K) beta 0).le
  calc
    (∑ s, isingWeight (freeDomainGraph K) beta 0 s / Z *
        (spin s x.1 * spin s
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) =
      (∑ s, isingWeight (freeDomainGraph K) beta 0 s *
        (spin s x.1 * spin s
          (isingDiagonalDomainReflectEquiv K i j hij c hK y.1))) / Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ <= (∑ s, isingWeight (freeDomainGraph K) beta 0 s *
        (spin s x.1 * spin s y.1)) / Z := by
      apply div_le_div_of_nonneg_right _ hZ
      rw [hcross, hsame]
      exact hfold
    _ = ∑ s, isingWeight (freeDomainGraph K) beta 0 s / Z *
        (spin s x.1 * spin s y.1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring

end Domain
end StatMech.FrontierA
