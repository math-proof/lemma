/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part9
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaBalancedOrbit.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaSwapRowsTag_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive
      (lpReplicaSwapRowsTag (G := G) (sites := sites) (m := m)) := by
  intro tag
  funext c
  rcases htag : tag c with ⟨row, current⟩
  cases row <;> cases current <;>
    simp [lpReplicaSwapRowsTag, htag]

set_option maxHeartbeats 800000 in
theorem lpReplicaCurrentCopies_swapRowsTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites m (lpReplicaSwapRowsTag tag) row current =
      lpReplicaCurrentCopies G sites m tag (!row) current := by
  ext c
  rcases htag : tag c with ⟨r, q⟩
  cases r <;> cases q <;> cases row <;> cases current <;>
    simp [lpReplicaCurrentCopies, lpReplicaSwapRowsTag, htag]

theorem lpReplicaRowCopies_swapRowsTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites m (lpReplicaSwapRowsTag tag) row =
      lpReplicaRowCopies G sites m tag (!row) := by
  ext c
  rcases htag : tag c with ⟨r, q⟩
  cases r <;> cases q <;> cases row <;>
    simp [lpReplicaRowCopies, lpReplicaSwapRowsTag, htag]


theorem lpReplicaRowGate_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    LPReplicaRowGate G sites m B A (lpReplicaSwapRowsTag tag) := by
  unfold LPReplicaRowGate at hgate ⊢
  simpa only [lpReplicaCurrentCopies_swapRowsTag,
    lpReplicaRowCopies_swapRowsTag, Bool.not_false, Bool.not_true] using
    ⟨hgate.2.2.2.1, hgate.2.2.2.2.1, hgate.2.2.2.2.2,
      hgate.1, hgate.2.1, hgate.2.2.1⟩


theorem lpReplicaRowGate_fullSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
      A ∆ B := by
  have hrows := lpReplicaRowGate_rowSources G sites m A B tag hgate
  have hunion : lpReplicaRowCopies G sites m tag false ∪
      lpReplicaRowCopies G sites m tag true = Finset.univ := by
    ext c
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, htag]
  have hdisj : Disjoint
      (lpReplicaRowCopies G sites m tag false)
      (lpReplicaRowCopies G sites m tag true) := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  rw [<- hunion, sources_union_of_disjoint hdisj, hrows.1, hrows.2]


theorem lpReplicaRowGate_totalSources_unique
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B C D : Finset (LPReplicaCurrentVertex V))
    (tag₁ tag₂ : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (h₁ : LPReplicaRowGate G sites m A B tag₁)
    (h₂ : LPReplicaRowGate G sites m C D tag₂) :
    A ∆ B = C ∆ D := by
  rw [<- lpReplicaRowGate_fullSources G sites m A B tag₁ h₁,
    <- lpReplicaRowGate_fullSources G sites m C D tag₂ h₂]


theorem lpReplicaRowGate_intermediate_ne_target
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag₁ tag₂ : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hmid : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      ∅ tag₁)
    (htarget : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag₂) : False := by
  have htotal := lpReplicaRowGate_totalSources_unique G sites m _ _ _ _
    tag₁ tag₂ hmid htarget
  have hg := Finset.ext_iff.mp htotal
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  simp [lpMatchingSeamSource, lpMatchingGhostSource,
    lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff] at hg


theorem lpReplicaRowGate_partialReflect_offdiag_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let movedTag := lpReplicaSwapRowsTag
      (lpReplicaPartialReflectTagRaw G sites m P tag)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (LPReplicaRowGate G sites target Si ∅ movedTag ∧
        (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨
      (LPReplicaRowGate G sites target Sj ∅ movedTag ∧
        (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
  dsimp only
  rcases lpReplicaRowGate_partialReflect_offdiag
      G sites hsite hij m tag hgate with h | h
  · left
    exact ⟨lpReplicaRowGate_swapRows G sites _ ∅ _ _ h.1, h.2⟩
  · right
    exact ⟨lpReplicaRowGate_swapRows G sites _ ∅ _ _ h.1, h.2⟩

end
end StatMech.Ising
