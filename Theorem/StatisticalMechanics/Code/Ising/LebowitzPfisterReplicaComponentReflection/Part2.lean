/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaGhostComponent.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


omit [Fintype I] [DecidableEq I] in


theorem lpReplicaOffdiagComponent_partialReflectSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let H := lpReplicaCurrentGraph G sites
    let K : Finset (Copy H m) := Finset.univ
    let e := endsM H m
    let C := RandomCurrent.compOf e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let A := lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    lpReplicaPartialReflectSource A C = lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∨
      lpReplicaPartialReflectSource A C = lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let K : Finset (Copy H m) := Finset.univ
  let e := endsM H m
  let C := RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C := by
    rw [RandomCurrent.mem_compOf]
    exact Relation.ReflTransGen.refl
  have hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C := by
    rw [RandomCurrent.mem_compOf]
    simpa [e, K, H] using hdisc
  have hsplit := lpReplicaGhostComponent_splits_exactly_one_markedSeam
    G sites hsite hij m hsrc hdisc
  have hsplitC :
      (((lpReplicaCurrentLeft sites i ∈ C ∧
            lpReplicaCurrentRight sites i ∉ C) ∨
          (lpReplicaCurrentLeft sites i ∉ C ∧
            lpReplicaCurrentRight sites i ∈ C)) ∧
        ¬ ((lpReplicaCurrentLeft sites j ∈ C ∧
            lpReplicaCurrentRight sites j ∉ C) ∨
          (lpReplicaCurrentLeft sites j ∉ C ∧
            lpReplicaCurrentRight sites j ∈ C))) ∨
      (¬ ((lpReplicaCurrentLeft sites i ∈ C ∧
            lpReplicaCurrentRight sites i ∉ C) ∨
          (lpReplicaCurrentLeft sites i ∉ C ∧
            lpReplicaCurrentRight sites i ∈ C)) ∧
        ((lpReplicaCurrentLeft sites j ∈ C ∧
            lpReplicaCurrentRight sites j ∉ C) ∨
          (lpReplicaCurrentLeft sites j ∉ C ∧
            lpReplicaCurrentRight sites j ∈ C))) := by
    simpa only [C, RandomCurrent.mem_compOf] using hsplit
  have hA := lpReplicaOffdiagSource_eq_six sites hsite hij
  rw [hA]
  rcases hsplitC with h | h
  · exact Or.inr (lpReplicaPartial_six_eq_seam_j sites hsite hij C
      hg0 hg1 h.1 h.2)
  · exact Or.inl (lpReplicaPartial_six_eq_seam_i sites hsite hij C
      hg0 hg1 h.1 h.2)

omit [Fintype V] in


theorem lpOffdiagPartialSource_complement
    (Si Sj T P : Finset (LPReplicaCurrentVertex V))
    (hP : P = Si ∨ P = Sj) :
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  rcases hP with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  · right
    refine ⟨rfl, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff]
    tauto

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaOffdiagComponent_partialReflectAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let H := lpReplicaCurrentGraph G sites
    let C := RandomCurrent.compOf (endsM H m)
      (Finset.univ : Finset (Copy H m))
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  dsimp only
  apply lpOffdiagPartialSource_complement
  exact lpReplicaOffdiagComponent_partialReflectSource
    G sites hsite hij m hsrc hdisc

end
end StatMech.Ising
