/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part42
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {x : Option (FK.boxVerts 3 n)} :
    x ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint ↔
      x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v ∧
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint
          ({x} : Finset (Option (FK.boxVerts 3 n)))).Nonempty := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_one_eq_singletonOptionNonemptyClassifiedSet_card_of_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v true true true 1).card =
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
        v Ω true true true).card := by
  classical
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ω true true true
  let sourceSet :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
      n Ω v true true true 1
  let marked :=
    finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true
  let singletonSource : Option (FK.boxVerts 3 n) →
      Finset (Option (FK.boxVerts 3 n)) :=
    fun x => marked ∪ ({x} : Finset (Option (FK.boxVerts 3 n)))
  have hsource_eq_image : sourceSet = liveOptions.image singletonSource := by
    ext S
    constructor
    · intro hS
      have hSmem :
          S ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
              n Ω v true true true 1 := by
        simpa [sourceSet] using hS
      rcases
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
          hSmem with
        ⟨hSsupport, hcase, hcard⟩
      let R := finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
      have hRpow :
          R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
        simpa [R] using
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset
            v S
      have hRcard : R.card = 1 := by
        simpa [R] using hcard
      rcases Finset.card_eq_one.mp hRcard with ⟨x, hRx⟩
      have hxU : x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v := by
        have hxR : x ∈ R := by
          simp [hRx]
        exact (Finset.mem_powerset.mp hRpow) hxR
      have hdecomp :
          marked ∪ R = S := by
        simpa [marked, R] using
          finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
            hcase
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · rw [
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff]
        refine ⟨hxU, ?_⟩
        rcases Finset.mem_image.mp hSsupport with ⟨E, hE, hEsource⟩
        refine ⟨E, ?_⟩
        rw [
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet_mem_iff]
        refine ⟨hE, ?_⟩
        calc
          E.1 = S := hEsource
          _ = marked ∪ R := hdecomp.symm
          _ =
              finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
                ({x} : Finset (Option (FK.boxVerts 3 n))) := by
              simp [marked, hRx]
      · simpa [singletonSource, marked, hRx] using hdecomp
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨x, hxLive, rfl⟩
      have hxlive' :
          x ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ω true true true := by
        simpa [liveOptions] using hxLive
      rcases
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff.mp
          hxlive' with
        ⟨hxU, hnonempty⟩
      have hsourceSupport :
          singletonSource x ∈
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
              n Ω v := by
        rcases hnonempty with ⟨E, hE⟩
        rcases
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet_mem_iff.mp
            hE with
          ⟨hEsupport, hEsource⟩
        exact Finset.mem_image.mpr
          ⟨E, hEsupport, by simpa [singletonSource, marked] using hEsource⟩
      have hRpow :
          ({x} : Finset (Option (FK.boxVerts 3 n))) ∈
            (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
        exact Finset.mem_powerset.mpr (by
          intro y hy
          have hyx : y = x := by
            simpa using hy
          simpa [hyx] using hxU)
      have hcardUnion :
          (singletonSource x).card = 4 := by
        have hmarkedCard :
            marked.card = 3 := by
          have hthreshold :=
            finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
              hv true true true
          have hthreshold' :
              finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                  true true true +
                marked.card =
              4 := by
            simpa [marked] using hthreshold
          have hthreshold'' : 1 + marked.card = 4 := by
            simpa [
              finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
              using hthreshold'
          omega
        have hunion :=
          finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
            v true true true hRpow
        have hunion' :
            (marked ∪ ({x} : Finset (Option (FK.boxVerts 3 n)))).card =
              marked.card +
                ({x} : Finset (Option (FK.boxVerts 3 n))).card := by
          simpa [marked] using hunion
        simpa [singletonSource, hmarkedCard] using hunion'
      have hcase :
          finiteBoundaryGhostSourceClassEndpointMembershipCase v
              (singletonSource x) =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus true true true := by
        change
          SourceClassEndpointMembershipCase.mk
              (finiteBoundaryGhostSourceClassCardinalityCase
                (singletonSource x))
              (decide (none ∈ singletonSource x))
              (decide
                (some (IsingFK.boxOrigin 3 n) ∈ singletonSource x))
              (decide (some v ∈ singletonSource x)) =
            SourceClassEndpointMembershipCase.mk
              SourceClassCardinalityCase.fourPlus true true true
        congr
        · simp [finiteBoundaryGhostSourceClassCardinalityCase, hcardUnion]
        · simp [
            singletonSource, marked,
            finiteBoundaryGhostSourceClassEndpointMarkedSources]
        · simp [
            singletonSource, marked,
            finiteBoundaryGhostSourceClassEndpointMarkedSources]
        · simp [
            singletonSource, marked,
            finiteBoundaryGhostSourceClassEndpointMarkedSources]
      have hresidual :
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v
              (singletonSource x) =
            ({x} : Finset (Option (FK.boxVerts 3 n))) := by
        ext y
        constructor
        · intro hy
          rcases
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mp
              hy with
            ⟨hySource, hyU⟩
          rcases Finset.mem_union.mp hySource with hymarked | hysingleton
          · have hynotU :=
              (Finset.disjoint_left.mp
                (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
                  v true true true)) hymarked
            exact False.elim (hynotU hyU)
          · exact hysingleton
        · intro hy
          rw [
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff]
          constructor
          · exact Finset.mem_union.mpr (Or.inr hy)
          · have hyx : y = x := by
              simpa using hy
            simpa [hyx] using hxU
      rw [
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff]
      refine ⟨hsourceSupport, hcase, ?_⟩
      simp [hresidual]
  have hinj :
      Set.InjOn singletonSource (liveOptions : Set (Option (FK.boxVerts 3 n))) := by
    intro x hx y hy hxy
    have hxLive :
        x ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
              v Ω true true true := by
      simpa [liveOptions] using hx
    have hyLive :
        y ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
              v Ω true true true := by
      simpa [liveOptions] using hy
    have hxU :
        x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff.mp
        hxLive).1
    have hyU :
        y ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff.mp
        hyLive).1
    have hxSourceRight : x ∈ marked ∪ ({y} : Finset (Option (FK.boxVerts 3 n))) := by
      have hxSourceLeft : x ∈ marked ∪ ({x} : Finset (Option (FK.boxVerts 3 n))) :=
        Finset.mem_union.mpr (Or.inr (by simp))
      have hxSourceLeft' : x ∈ singletonSource x := by
        simp [singletonSource]
      have hxSourceRight' : x ∈ singletonSource y := by
        simpa [hxy] using hxSourceLeft'
      simpa [singletonSource] using hxSourceRight'
    have hxmem : x ∈ ({y} : Finset (Option (FK.boxVerts 3 n))) := by
      rcases Finset.mem_union.mp hxSourceRight with hxmarked | hxsingleton
      · have hxnotU :=
          (Finset.disjoint_left.mp
            (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
              v true true true)) hxmarked
        exact False.elim (hxnotU hxU)
      · exact hxsingleton
    simpa using hxmem
  calc
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v true true true 1).card = sourceSet.card := by
        rfl
    _ = (liveOptions.image singletonSource).card := by
        rw [hsource_eq_image]
    _ = liveOptions.card :=
        Finset.card_image_of_injOn (s := liveOptions) (f := singletonSource) hinj
    _ =
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
          v Ω true true true).card := by
        rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_one_cast_eq_singletonOptionNonemptyClassifiedSet_card_of_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v true true true 1).card : ℝ) =
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
        v Ω true true true).card : ℝ) := by
  exact_mod_cast
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_one_eq_singletonOptionNonemptyClassifiedSet_card_of_boundary
      Ω hv

end Exact3D
end StatMech
