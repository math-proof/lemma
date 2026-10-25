/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part6
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem selectedOptionSpin_ne_iff_not_even
    {α : Type*} [DecidableEq α] (S : Finset α)
    {u v : Option α} (huv : u ≠ v) :
    selectedOptionSpin S u ≠ selectedOptionSpin S v ↔
      ¬ Even ((S.filter fun q => q ∈ u.toFinset ∪ v.toFinset).card) := by
  cases u with
  | none =>
      cases v with
      | none => exact False.elim (huv rfl)
      | some y =>
          simp only [selectedOptionSpin, Option.toFinset_none,
            Option.toFinset_some, empty_union, mem_singleton]
          rw [Finset.filter_eq' S y]
          by_cases hy : y ∈ S <;> simp [hy]
  | some x =>
      cases v with
      | none =>
          simp only [selectedOptionSpin, Option.toFinset_none,
            Option.toFinset_some, union_empty, mem_singleton]
          rw [Finset.filter_eq' S x]
          by_cases hx : x ∈ S <;> simp [hx]
      | some y =>
          have hxy : x ≠ y := by
            intro h
            exact huv (by simp [h])
          simp only [selectedOptionSpin, Option.toFinset_some,
            mem_union, mem_singleton]
          rw [Finset.filter_or, Finset.filter_eq' S x,
            Finset.filter_eq' S y]
          by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
            simp [hx, hy, hxy]

@[simp] theorem finBackward_eq_none_iff {n : Nat} (f : Fin (n + 1)) :
    finBackward f = none ↔ f = 0 := by
  refine Fin.cases ?_ (fun z => ?_) f
  · simp [finBackward]
  · simp [finBackward]

theorem finBackward_ne_finForward {n : Nat} (hn : 0 < n)
    (f : Fin (n + 1)) :
    finBackward f ≠ finForward f := by
  intro h
  cases hb : finBackward f with
  | none =>
      have hf : f = 0 := (finBackward_eq_none_iff f).mp hb
      subst f
      let z : Fin n := ⟨0, hn⟩
      have hforward : finForward (0 : Fin (n + 1)) = some z :=
        (finForward_eq_some_iff 0 z).mpr (Fin.ext (by simp [z]))
      simp [hb, hforward] at h
  | some k =>
      have hforward : finForward f = some k := by
        rw [← h]
        exact hb
      have hsucc : f = k.succ := (finBackward_eq_some_iff f k).mp hb
      have hcast : f = k.castSucc :=
        (finForward_eq_some_iff f k).mp hforward
      have hv := congrArg Fin.val (hsucc.symm.trans hcast)
      simp at hv

theorem cubicalDualEnds_ne {a b c : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p : CubicalPlaquette a b c) :
    (cubicalDualEnds p).1 ≠ (cubicalDualEnds p).2 := by
  cases p with
  | xy i j k =>
      intro h
      apply finBackward_ne_finForward hc k
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.z h) h
  | xz i j k =>
      intro h
      apply finBackward_ne_finForward hb j
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.y h) h
  | yz i j k =>
      intro h
      apply finBackward_ne_finForward ha i
      exact Option.map_injective (fun _ _ h => congrArg CubicalCell.x h) h

@[simp] theorem cellFinsetAnchoredEquiv_apply
    {a b c : Nat} (S : Finset (CubicalCell a b c))
    (q : Option (CubicalCell a b c)) :
    (cellFinsetAnchoredEquiv S).1 q = selectedOptionSpin S q := by
  cases q <;> rfl


theorem multibondCut_cellFinsetAnchored_eq_volumeBoundary
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (S : Finset (CubicalCell a b c)) :
    multibondCut cubicalDualEnds (cellFinsetAnchoredEquiv S).1 =
      cubicalVolumeBoundary S := by
  ext p
  rw [mem_multibondCut, cubicalVolumeBoundary, mem_gaugeSurfaceBoundary,
    plaquetteIncidenceCount_cellFaces_eq]
  simpa [cubicalPlaquetteCells] using
    (selectedOptionSpin_ne_iff_not_even S (cubicalDualEnds_ne ha hb hc p))


end
end StatMech.FrontierA
