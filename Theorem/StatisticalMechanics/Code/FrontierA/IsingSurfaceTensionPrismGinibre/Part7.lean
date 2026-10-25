/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem oddPrismReverseVerticalChain_end_ne
    (n : Nat) (hn : 0 < n) :
    oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0 ≠
      oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n) := by
  intro h
  have hz := congrArg (fun v => v.z.val) h
  simp [oddPrismReverseVerticalChain] at hz
  omega

theorem oddPrismPlusField_reverse_top (n : Nat) (hn : 0 < n) :
    oddPrismPlusField n
        (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0) = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 * n := by omega
  simp [oddPrismPlusField, oddPrismReverseVerticalChain, oddPrismCenter,
    rectangularPrismBoundaryDegree, hn0, hn2]

theorem oddPrismDobrushinField_reverse_top (n : Nat) (hn : 0 < n) :
    oddPrismDobrushinField n
        (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0) = -1 := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 * n := by omega
  have hnlt : n < 2 * n := by omega
  simp [oddPrismDobrushinField, oddPrismReverseVerticalChain, oddPrismCenter,
    oddRectangularPrismDobrushinSign, rectangularPrismBoundaryDegree,
    hn0, hn2, hnlt]

theorem oddPrismPlusField_reverse_bottom (n : Nat) (hn : 0 < n) :
    oddPrismPlusField n
        (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n)) = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 * n := by omega
  simp [oddPrismPlusField, oddPrismReverseVerticalChain, oddPrismCenter,
    rectangularPrismBoundaryDegree, hn0, hn2]

theorem oddPrismDobrushinField_reverse_bottom (n : Nat) (hn : 0 < n) :
    oddPrismDobrushinField n
        (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n)) = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 * n := by omega
  simp [oddPrismDobrushinField, oddPrismReverseVerticalChain, oddPrismCenter,
    oddRectangularPrismDobrushinSign, rectangularPrismBoundaryDegree,
    hn0, hn2]


theorem oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalAbsCross
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    let v := oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n)
    (oddPrismPlusSpinMean beta n (v 0) +
        oddPrismDobrushinSpinMean beta n (v 0)) +
      (∑ j : Fin (2 * n),
        |oddPrismPlusSpinMean beta n (v j.val) *
            oddPrismDobrushinSpinMean beta n (v (j.val + 1)) -
          oddPrismPlusSpinMean beta n (v (j.val + 1)) *
            oddPrismDobrushinSpinMean beta n (v j.val)|) +
      (oddPrismPlusSpinMean beta n (v (2 * n)) -
        oddPrismDobrushinSpinMean beta n (v (2 * n))) <=
      deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n) beta := by
  dsimp only
  have h := boundaryInterfaceFreeEnergy_deriv_ge_extendedChainAbsCross
    (oddPrismInternalEdges n) (fun _ => 1)
    (oddPrismPlusField n) (oddPrismDobrushinField n)
    (fun _ _ => by norm_num)
    (abs_oddPrismDobrushinField_le_plusField n)
    beta hbeta
    (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n))
    (2 * n)
    (ginibreChainEdge_oddPrismReverseVerticalChain_injective n _ _)
    (ginibreChainEdge_oddPrismReverseVerticalChain_mem n _ _)
    (fun _ => rfl)
    (oddPrismReverseVerticalChain_end_ne n hn)
    (oddPrismPlusField_reverse_top n hn)
    (oddPrismDobrushinField_reverse_top n hn)
    (oddPrismPlusField_reverse_bottom n hn)
    (oddPrismDobrushinField_reverse_bottom n hn)
  have hfree :
      boundaryInterfaceFreeEnergy (oddPrismInternalEdges n) (fun _ => 1)
          (oddPrismPlusField n) (oddPrismDobrushinField n) =
        fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
          (2 * n + 1) (2 * n + 1) n := by
    funext b
    exact boundaryInterfaceFreeEnergy_oddPrism_eq b n
  rw [hfree] at h
  simpa [oddPrismPlusSpinMean, oddPrismDobrushinSpinMean] using h

theorem abs_oddPrismDobrushinSpinMean_le_plusSpinMean
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    |oddPrismDobrushinSpinMean beta n v| <=
      oddPrismPlusSpinMean beta n v := by
  apply ginibre_boundary_abs_onePoint_le
    (oddPrismInternalEdges n) (fun _ => beta)
    (fun x => beta * oddPrismPlusField n x)
    (fun x => beta * oddPrismDobrushinField n x)
  · intro _ _
    exact hbeta
  · intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left
      (abs_oddPrismDobrushinField_le_plusField n x) hbeta

theorem magnetization_le_oddPrismPlusSpinMean
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    magnetization 3 beta <= oddPrismPlusSpinMean beta n v := by
  rw [oddPrismPlusSpinMean_eq_plusMeasure_integral]
  exact magnetization_le_plusMeasure_spin beta hbeta n
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1


theorem oddPrismDobrushinFreeEnergy_deriv_ge_two_mul_magnetization_sq
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    2 * magnetization 3 beta ^ 2 <=
      deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n) beta := by
  let v := oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n)
  let p : Fin (2 * n + 1) -> Real := fun j =>
    oddPrismPlusSpinMean beta n (v j.val)
  let q : Fin (2 * n + 1) -> Real := fun j =>
    oddPrismDobrushinSpinMean beta n (v j.val)
  have halg := extendedChain_absCross_ge_two_mul_sq (2 * n) p q
    (magnetization 3 beta)
    (StatMech.IsingFK.magnetization_nonneg 3 hbeta)
    (magnetization_le_one 3 beta)
    (fun j => magnetization_le_oddPrismPlusSpinMean beta hbeta n (v j.val))
    (fun j => abs_oddPrismDobrushinSpinMean_le_plusSpinMean
      beta hbeta n (v j.val))
  have hderiv :=
    oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalAbsCross
      beta hbeta n hn
  exact halg.trans (by simpa [p, q, v] using hderiv)

theorem ginibreChainEdge_oddPrismReverseVerticalFamily_injective
    (n : Nat) :
    Function.Injective (fun q :
      (Fin (2 * n + 1) × Fin (2 * n + 1)) × Fin (2 * n) =>
        ginibreChainEdge
          (oddPrismReverseVerticalChain n q.1.1 q.1.2) q.2) := by
  intro a b hab
  change ginibreChainEdge
      (oddPrismReverseVerticalChain n a.1.1 a.1.2) a.2 =
    ginibreChainEdge
      (oddPrismReverseVerticalChain n b.1.1 b.1.2) b.2 at hab
  rw [ginibreChainEdge_oddPrismReverseVerticalChain,
    ginibreChainEdge_oddPrismReverseVerticalChain] at hab
  have hq := oddPrismInternalEdge_injective n hab
  have h1 :
      (Sum.inr (a.1.1, a.1.2, oddPrismReverseVerticalEdgeIndex n a.2) :
        (Fin (2 * n + 1) × Fin (2 * n) × Fin (2 * n + 1)) ⊕
          (Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (2 * n))) =
        Sum.inr (b.1.1, b.1.2, oddPrismReverseVerticalEdgeIndex n b.2) :=
    Sum.inr.inj hq
  have h2 :
      (a.1.1, a.1.2, oddPrismReverseVerticalEdgeIndex n a.2) =
        (b.1.1, b.1.2, oddPrismReverseVerticalEdgeIndex n b.2) :=
    Sum.inr.inj h1
  have hx : a.1.1 = b.1.1 := congrArg (fun z => z.1) h2
  have hy : a.1.2 = b.1.2 := congrArg (fun z => z.2.1) h2
  have hz := congrArg (fun z => z.2.2.val) h2
  have hj : a.2 = b.2 := by
    apply Fin.ext
    dsimp [oddPrismReverseVerticalEdgeIndex] at hz
    omega
  exact Prod.ext (Prod.ext hx hy) hj

theorem oddPrismReverseVerticalFamily_end_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fun z :
      (Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
        (Fin (2 * n + 1) × Fin (2 * n + 1)) =>
      match z with
      | .inl i => oddPrismReverseVerticalChain n i.1 i.2 0
      | .inr i => oddPrismReverseVerticalChain n i.1 i.2 (2 * n)) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    apply Prod.ext
    · exact congrArg (fun z => z.x) hab
    · exact congrArg (fun z => z.y) hab
  · have hz := congrArg (fun z => z.z.val) hab
    simp [oddPrismReverseVerticalChain] at hz
    omega
  · have hz := congrArg (fun z => z.z.val) hab
    simp [oddPrismReverseVerticalChain] at hz
    omega
  · apply congrArg Sum.inr
    apply Prod.ext
    · exact congrArg (fun z => z.x) hab
    · exact congrArg (fun z => z.y) hab

theorem oddPrismPlusField_reverse_top_ge_one
    (n : Nat) (x y : Fin (2 * n + 1)) :
    1 <= oddPrismPlusField n (oddPrismReverseVerticalChain n x y 0) := by
  norm_cast
  unfold oddPrismPlusField rectangularPrismBoundaryDegree
  simp [oddPrismReverseVerticalChain]
  positivity

theorem oddPrismDobrushinField_reverse_top_eq_neg
    (n : Nat) (hn : 0 < n) (x y : Fin (2 * n + 1)) :
    oddPrismDobrushinField n (oddPrismReverseVerticalChain n x y 0) =
      -oddPrismPlusField n (oddPrismReverseVerticalChain n x y 0) := by
  have hnlt : n < 2 * n := by omega
  unfold oddPrismDobrushinField oddPrismPlusField
    oddRectangularPrismDobrushinSign
  simp [oddPrismReverseVerticalChain, hnlt]

theorem oddPrismPlusField_reverse_bottom_ge_one
    (n : Nat) (x y : Fin (2 * n + 1)) :
    1 <= oddPrismPlusField n
      (oddPrismReverseVerticalChain n x y (2 * n)) := by
  norm_cast
  unfold oddPrismPlusField rectangularPrismBoundaryDegree
  simp [oddPrismReverseVerticalChain]
  let a : Real := if x = 0 then 1 else 0
  let b : Real := if x.val = 2 * n then 1 else 0
  let c : Real := if y = 0 then 1 else 0
  let d : Real := if y.val = 2 * n then 1 else 0
  let e : Real := if n = 0 then 1 else 0
  change 1 <= (((a + b) + c) + d) + 1 + e
  have ha : 0 <= a := by dsimp [a]; split <;> norm_num
  have hb : 0 <= b := by dsimp [b]; split <;> norm_num
  have hc : 0 <= c := by dsimp [c]; split <;> norm_num
  have hd : 0 <= d := by dsimp [d]; split <;> norm_num
  have he : 0 <= e := by dsimp [e]; split <;> norm_num
  linarith

theorem oddPrismDobrushinField_reverse_bottom_eq
    (n : Nat) (x y : Fin (2 * n + 1)) :
    oddPrismDobrushinField n
        (oddPrismReverseVerticalChain n x y (2 * n)) =
      oddPrismPlusField n
        (oddPrismReverseVerticalChain n x y (2 * n)) := by
  unfold oddPrismDobrushinField oddPrismPlusField
    oddRectangularPrismDobrushinSign
  simp [oddPrismReverseVerticalChain]


theorem oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalFamily
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    (∑ i : Fin (2 * n + 1) × Fin (2 * n + 1),
      let v := oddPrismReverseVerticalChain n i.1 i.2
      ((oddPrismPlusSpinMean beta n (v 0) +
          oddPrismDobrushinSpinMean beta n (v 0)) +
        (∑ j : Fin (2 * n),
          |oddPrismPlusSpinMean beta n (v j.val) *
              oddPrismDobrushinSpinMean beta n (v (j.val + 1)) -
            oddPrismPlusSpinMean beta n (v (j.val + 1)) *
              oddPrismDobrushinSpinMean beta n (v j.val)|) +
        (oddPrismPlusSpinMean beta n (v (2 * n)) -
          oddPrismDobrushinSpinMean beta n (v (2 * n))))) <=
      deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n) beta := by
  have h := boundaryInterfaceFreeEnergy_deriv_ge_extendedChainFamilyAbsCross
    (I := Fin (2 * n + 1) × Fin (2 * n + 1))
    (oddPrismInternalEdges n) (fun _ => 1)
    (oddPrismPlusField n) (oddPrismDobrushinField n)
    (fun _ _ => by norm_num)
    (abs_oddPrismDobrushinField_le_plusField n)
    beta hbeta
    (fun i => oddPrismReverseVerticalChain n i.1 i.2) (2 * n)
    (ginibreChainEdge_oddPrismReverseVerticalFamily_injective n)
    (fun i => ginibreChainEdge_oddPrismReverseVerticalChain_mem n i.1 i.2)
    (fun _ _ => rfl)
    (by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · apply congrArg Sum.inl
        apply Prod.ext
        · exact congrArg (fun z => z.x) hab
        · exact congrArg (fun z => z.y) hab
      · have hz := congrArg (fun z => z.z.val) hab
        simp [oddPrismReverseVerticalChain] at hz
        omega
      · have hz := congrArg (fun z => z.z.val) hab
        simp [oddPrismReverseVerticalChain] at hz
        omega
      · apply congrArg Sum.inr
        apply Prod.ext
        · exact congrArg (fun z => z.x) hab
        · exact congrArg (fun z => z.y) hab)
    (fun i => oddPrismPlusField_reverse_top_ge_one n i.1 i.2)
    (fun i => oddPrismDobrushinField_reverse_top_eq_neg n hn i.1 i.2)
    (fun i => oddPrismPlusField_reverse_bottom_ge_one n i.1 i.2)
    (fun i => oddPrismDobrushinField_reverse_bottom_eq n i.1 i.2)
  have hfree :
      boundaryInterfaceFreeEnergy (oddPrismInternalEdges n) (fun _ => 1)
          (oddPrismPlusField n) (oddPrismDobrushinField n) =
        fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
          (2 * n + 1) (2 * n + 1) n := by
    funext b
    exact boundaryInterfaceFreeEnergy_oddPrism_eq b n
  rw [hfree] at h
  simpa [oddPrismPlusSpinMean, oddPrismDobrushinSpinMean] using h


theorem oddPrismDobrushinFreeEnergy_deriv_ge_area_mul_two_mul_sq
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    (((2 * n + 1 : Nat) : Real) ^ 2) *
        (2 * magnetization 3 beta ^ 2) <=
      deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n) beta := by
  let chainValue : Fin (2 * n + 1) × Fin (2 * n + 1) -> Real := fun i =>
    let v := oddPrismReverseVerticalChain n i.1 i.2
    (oddPrismPlusSpinMean beta n (v 0) +
        oddPrismDobrushinSpinMean beta n (v 0)) +
      (∑ j : Fin (2 * n),
        |oddPrismPlusSpinMean beta n (v j.val) *
            oddPrismDobrushinSpinMean beta n (v (j.val + 1)) -
          oddPrismPlusSpinMean beta n (v (j.val + 1)) *
            oddPrismDobrushinSpinMean beta n (v j.val)|) +
      (oddPrismPlusSpinMean beta n (v (2 * n)) -
        oddPrismDobrushinSpinMean beta n (v (2 * n)))
  have hcol (i : Fin (2 * n + 1) × Fin (2 * n + 1)) :
      2 * magnetization 3 beta ^ 2 <= chainValue i := by
    let v := oddPrismReverseVerticalChain n i.1 i.2
    let p : Fin (2 * n + 1) -> Real := fun j =>
      oddPrismPlusSpinMean beta n (v j.val)
    let q : Fin (2 * n + 1) -> Real := fun j =>
      oddPrismDobrushinSpinMean beta n (v j.val)
    have h := extendedChain_absCross_ge_two_mul_sq (2 * n) p q
      (magnetization 3 beta)
      (StatMech.IsingFK.magnetization_nonneg 3 hbeta)
      (magnetization_le_one 3 beta)
      (fun j => magnetization_le_oddPrismPlusSpinMean beta hbeta n (v j.val))
      (fun j => abs_oddPrismDobrushinSpinMean_le_plusSpinMean
        beta hbeta n (v j.val))
    simpa [chainValue, p, q, v] using h
  have hsum :
      (∑ _i : Fin (2 * n + 1) × Fin (2 * n + 1),
        2 * magnetization 3 beta ^ 2) <= ∑ i, chainValue i :=
    Finset.sum_le_sum fun i _ => hcol i
  have hfamily :=
    oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalFamily
      beta hbeta n hn
  have hcard :
      (∑ _i : Fin (2 * n + 1) × Fin (2 * n + 1),
        2 * magnetization 3 beta ^ 2) =
      (((2 * n + 1 : Nat) : Real) ^ 2) *
        (2 * magnetization 3 beta ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
    simp only [Fintype.card_fin, nsmul_eq_mul]
    norm_cast
    ring
  rw [hcard] at hsum
  exact hsum.trans (by simpa [chainValue] using hfamily)


theorem finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    2 * magnetization 3 beta ^ 2 *
        (((2 * n + 1 : Nat) : Real) ^ 2) <=
      fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 -
        fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n
          (bondFinsetTouch 3 n) beta 0 := by
  have h := oddPrismDobrushinFreeEnergy_deriv_ge_area_mul_two_mul_sq
    beta hbeta n hn
  rw [(hasDerivAt_oddPrismDobrushinFreeEnergy 1 beta n hn).deriv] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h


theorem standardCubicInterfaceDensity_deriv_ge_two_mul_sq_via_prism
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    2 * magnetization 3 beta ^ 2 <=
      deriv (fun b => standardCubicInterfaceDensity b n) beta := by
  let area : Real := ((2 * n + 1 : Nat) : Real) ^ 2
  have hfun : (fun b => standardCubicInterfaceDensity b n) =
      fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n / area := by
    funext b
    unfold standardCubicInterfaceDensity
    dsimp [area]
    congr 1
    simpa using
      (oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy 1 b n hn).symm
  have harea : 0 < area := by
    dsimp [area]
    positivity
  rw [hfun,
    ((hasDerivAt_oddPrismDobrushinFreeEnergy 1 beta n hn).div_const area).deriv]
  rw [le_div_iff₀ harea]
  simpa [area, mul_comm, mul_left_comm, mul_assoc] using
    finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq
      beta hbeta n hn


theorem oddPrismDobrushinFreeEnergy_deriv_ge_verticalChainCross
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (x y : Fin (2 * n + 1)) :
    (∑ j : Fin (2 * n),
      (oddPrismPlusSpinMean beta n (oddPrismVerticalChain n x y j.val) *
          oddPrismDobrushinSpinMean beta n
            (oddPrismVerticalChain n x y (j.val + 1)) -
        oddPrismPlusSpinMean beta n
            (oddPrismVerticalChain n x y (j.val + 1)) *
          oddPrismDobrushinSpinMean beta n
            (oddPrismVerticalChain n x y j.val))) <=
      deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
        (2 * n + 1) (2 * n + 1) n) beta := by
  have h := boundaryInterfaceFreeEnergy_deriv_ge_chainCross
    (oddPrismInternalEdges n) (fun _ => 1)
    (oddPrismPlusField n) (oddPrismDobrushinField n)
    (fun _ _ => by norm_num)
    (abs_oddPrismDobrushinField_le_plusField n)
    beta hbeta (oddPrismVerticalChain n x y) (2 * n)
    (ginibreChainEdge_oddPrismVerticalChain_injective n x y)
    (ginibreChainEdge_oddPrismVerticalChain_mem n x y)
    (fun _ => rfl)
  have hfree :
      boundaryInterfaceFreeEnergy (oddPrismInternalEdges n) (fun _ => 1)
          (oddPrismPlusField n) (oddPrismDobrushinField n) =
        fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b
          (2 * n + 1) (2 * n + 1) n := by
    funext b
    exact boundaryInterfaceFreeEnergy_oddPrism_eq b n
  rw [hfree] at h
  simpa [oddPrismPlusSpinMean, oddPrismDobrushinSpinMean] using h

end
end StatMech.FrontierA
