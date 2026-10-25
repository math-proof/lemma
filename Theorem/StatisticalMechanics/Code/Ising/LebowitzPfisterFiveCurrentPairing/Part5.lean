/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


theorem lpMatchingDisconnCenteredGram_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    lpMatchingDisconnCenteredGram G beta J left right g0 g1 =
      sourcePairDisconnSum G beta J ∅ ∅ g0 g1 *
          lpMatchingDisconnTwo G beta J left right g0 g1 -
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1 := by
  unfold lpMatchingDisconnCenteredGram lpMatchingDisconnTwo
    lpMatchingDisconnZero lpMatchingDisconnOne
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem lpMatchingDisconnZero_eq_currentGap
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    lpMatchingDisconnZero G beta J left right g0 g1 =
      (∑ i : I, currentSum G beta J
          (lpMatchingSeamSource left right i)) * currentSum G beta J ∅ -
        (∑ i : I, currentSum G beta J
          (lpMatchingSeamSource left right i ∆ T)) *
            currentSum G beta J T := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  unfold lpMatchingDisconnZero
  calc
    _ = ∑ i : I,
        (currentSum G beta J (lpMatchingSeamSource left right i) *
            currentSum G beta J ∅ -
          currentSum G beta J
              (lpMatchingSeamSource left right i ∆ T) *
            currentSum G beta J T) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := gcr_currentSum_ghostRep G beta J
        (lpMatchingSeamSource left right i) hg
      rw [← hT] at h
      exact h.symm
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]


theorem lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    (∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) =
      Z * ((Z ^ 2 - C ^ 2) *
          lpMatchingDisconnTwo G beta J left right g0 g1 -
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1) := by
  dsimp only
  simp_rw [lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues
    G beta J left right g0 g1 hg]
  rw [lpMatchingDisconnZero_eq_currentGap
    G beta J left right g0 g1 hg]
  unfold lpMatchingDisconnOne lpMatchingDisconnTwo
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) <= 0) <->
      (Z ^ 2 - C ^ 2) *
          lpMatchingDisconnTwo G beta J left right g0 g1 <=
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1 := by
  dsimp only
  rw [lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap
    G beta J left right g0 g1 hg]
  have hZ : 0 < currentSum G beta J ∅ :=
    acr_currentSum_empty_pos G beta J
  constructor
  · intro h
    have hx :
        (currentSum G beta J ∅ ^ 2 -
            currentSum G beta J (lpMatchingGhostSource g0 g1) ^ 2) *
              lpMatchingDisconnTwo G beta J left right g0 g1 -
          2 * lpMatchingDisconnZero G beta J left right g0 g1 *
            lpMatchingDisconnOne G beta J left right g0 g1 <= 0 := by
      nlinarith
    exact sub_nonpos.mp hx
  · intro h
    have hx := sub_nonpos.mpr h
    nlinarith


theorem lpGhostCurrentSquareGap_eq_emptyDisconn
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 =
      sourcePairDisconnSum G beta J ∅ ∅ g0 g1 := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have h := gcr_currentSum_ghostRep G beta J (∅ : Finset W) hg
  rw [← hT] at h
  have hempty : (∅ : Finset W) ∆ T = T := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hempty] at h
  simpa [pow_two] using h


theorem lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) <= 0) <->
      lpMatchingDisconnCenteredGram G beta J
        left right g0 g1 <= 0 := by
  have hsign := lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    G beta J left right g0 g1 hg
  dsimp only at hsign
  rw [hsign]
  rw [← sub_nonpos]
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn G beta J g0 g1 hg]
  rw [← lpMatchingDisconnCenteredGram_eq]


theorem lpSourcePairDisconnSum_nonneg
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (A B : Finset W) (u v : W) :
    0 <= sourcePairDisconnSum G beta J A B u v := by
  unfold sourcePairDisconnSum
  apply tsum_nonneg
  rintro ⟨p, q⟩
  by_cases hp : StatMech.Sharpness.sources G (ofEdgeFun G p) = A <;>
    by_cases hq : StatMech.Sharpness.sources G (ofEdgeFun G q) = B <;>
    by_cases hc : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => p e + q e)) u v <;>
    simp [hp, hq, hc]
  exact mul_nonneg
    (acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G p))
    (acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G q))


theorem lpGhostCurrentSquareGap_nonneg
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    0 <= currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 := by
  dsimp only
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn G beta J g0 g1 hg]
  exact lpSourcePairDisconnSum_nonneg G beta J hbeta hJ ∅ ∅ g0 g1


theorem lpGhostSourceDisconn_eq_zero
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    sourcePairDisconnSum G beta J T ∅ g0 g1 = 0 := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have h := gcr_currentSum_ghostRep G beta J T hg
  rw [← hT, symmDiff_self] at h
  dsimp only [T] at h ⊢
  calc
    _ = currentSum G beta J (lpMatchingGhostSource g0 g1) *
          currentSum G beta J ∅ -
        currentSum G beta J ∅ *
          currentSum G beta J (lpMatchingGhostSource g0 g1) := h.symm
    _ = 0 := by ring


theorem lpMatchingDisconn_diagonal_le
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1)
    (i : I) :
    let Si := lpMatchingSeamSource left right i
    let T := lpMatchingGhostSource g0 g1
    sourcePairDisconnSum G beta J ∅ ∅ g0 g1 *
        sourcePairDisconnSum G beta J (Si ∆ Si ∆ T) ∅ g0 g1 <=
      2 * sourcePairDisconnSum G beta J Si ∅ g0 g1 *
        sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 := by
  dsimp only
  let Si := lpMatchingSeamSource left right i
  let T := lpMatchingGhostSource g0 g1
  have hsource : Si ∆ Si ∆ T = T := by
    rw [symmDiff_self]
    ext x
    simp [Finset.mem_symmDiff]
  rw [hsource, lpGhostSourceDisconn_eq_zero G beta J g0 g1 hg,
    mul_zero]
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (lpSourcePairDisconnSum_nonneg G beta J hbeta hJ Si ∅ g0 g1))
    (lpSourcePairDisconnSum_nonneg G beta J hbeta hJ (Si ∆ T) ∅ g0 g1)


theorem lpMatchingDisconnTwo_eq_offDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    lpMatchingDisconnTwo G beta J left right g0 g1 =
      lpMatchingDisconnTwoOffDiag G beta J left right g0 g1 := by
  unfold lpMatchingDisconnTwo lpMatchingDisconnTwoOffDiag
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hsource :
        lpMatchingSeamSource left right i ∆
            lpMatchingSeamSource left right i ∆
            lpMatchingGhostSource g0 g1 =
          lpMatchingGhostSource g0 g1 := by
      rw [symmDiff_self]
      ext x
      simp [Finset.mem_symmDiff]
    rw [hsource, lpGhostSourceDisconn_eq_zero G beta J g0 g1 hg]
  · rw [if_neg hij]

end
end StatMech.Ising
