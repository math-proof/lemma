/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part3
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

@[simp] theorem ons_plusDualContourFace_map_val (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    (ons_plusDualContourFace n tau).image (Sym2.map Subtype.val) =
      ons_plusDualContour n tau := by
  ext edge
  simp only [ons_plusDualContourFace, Finset.mem_image, Finset.mem_map,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨lifted, ⟨source, hsource, rfl⟩, rfl⟩
    simpa using hsource
  · intro hedge
    let source : {edge // edge ∈ ons_plusDualContour n tau} := ⟨edge, hedge⟩
    refine ⟨ons_plusDualFaceEdgeLift n
        ⟨source.1, ons_plusDualContour_subset_plusDualFaceEdgeSet
          n tau source.1 source.2⟩, ?_, ?_⟩
    · exact ⟨source, rfl⟩
    · exact ons_plusDualFaceEdgeLift_map_val n _


theorem ons_plusDualContourFace_isEven (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    IsEvenSubgraph (ons_plusDualContourFace n tau) := by
  intro f
  have hglobal := ons_plusDualContour_isEven n tau f.1
  have hfilter :
      (ons_plusDualContour n tau).filter
          (fun edge => kwg_incidentMod2 f.1 edge) =
        (ons_plusDualContour n tau).filter (fun edge => f.1 ∈ edge) := by
    ext edge
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hedge
    have hedgeLat : edge ∈ (hypercubicLattice 2).edgeSet := by
      exact (ons_plusDualContour_subset_plusDualFaceEdgeSet
        n tau edge hedge).1
    induction edge using Sym2.inductionOn with
    | _ x y =>
        have hxy : x ≠ y :=
          ((SimpleGraph.mem_edgeSet _).mp hedgeLat).ne
        rw [kwg_incidentMod2_mk, Sym2.mem_iff]
        constructor <;> grind
  change Even (incCount (ons_plusDualContourFace n tau) f)
  change Even ((ons_plusDualContourFace n tau).filter (fun edge => f ∈ edge)).card
  change Even ((ons_plusDualContour n tau).filter
    (fun edge => kwg_incidentMod2 f.1 edge)).card at hglobal
  rw [hfilter] at hglobal
  have hcard :
      ((ons_plusDualContourFace n tau).filter (fun edge => f ∈ edge)).card =
        ((ons_plusDualContour n tau).filter (fun edge => f.1 ∈ edge)).card := by
    apply Finset.card_bij (fun edge _ => Sym2.map Subtype.val edge)
    · intro edge hedge
      rw [Finset.mem_filter] at hedge ⊢
      refine ⟨?_, ?_⟩
      · have himage : Sym2.map Subtype.val edge ∈
            (ons_plusDualContourFace n tau).image (Sym2.map Subtype.val) :=
          Finset.mem_image.mpr ⟨edge, hedge.1, rfl⟩
        simpa [ons_plusDualContourFace_map_val] using himage
      · exact (Sym2.mem_map).2 ⟨f, hedge.2, rfl⟩
    · intro a ha b hb hab
      exact Sym2.map.injective Subtype.val_injective hab
    · intro edge hedge
      rw [Finset.mem_filter] at hedge
      have hcontour : edge ∈ ons_plusDualContour n tau := hedge.1
      have hsupp := ons_plusDualContour_subset_plusDualFaceEdgeSet
        n tau edge hcontour
      let source : {edge // edge ∈ ons_plusDualContour n tau} :=
        ⟨edge, hcontour⟩
      let lifted := ons_plusDualFaceEdgeLift n ⟨edge, hsupp⟩
      refine ⟨lifted, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_map.mpr ⟨source, Finset.mem_attach _ _, rfl⟩
        · have hmapped : f.1 ∈ Sym2.map Subtype.val lifted := by
            rw [show Sym2.map Subtype.val lifted = edge by
              exact ons_plusDualFaceEdgeLift_map_val n _]
            exact hedge.2
          rw [Sym2.mem_map] at hmapped
          obtain ⟨g, hg, hgf⟩ := hmapped
          have hgf' : g = f := Subtype.ext hgf
          rwa [hgf'] at hg
      · exact ons_plusDualFaceEdgeLift_map_val n _
  rw [hcard]
  exact hglobal


end
end StatMech.Onsager
