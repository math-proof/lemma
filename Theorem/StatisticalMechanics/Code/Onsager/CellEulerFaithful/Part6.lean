/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part6


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem interior_representatives_reachable {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (BaseCase.pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (c e : interiorCells d hclosed hsimple hreflexfree) :
    (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Reachable
      (skeletonRepresentative _ c) (skeletonRepresentative _ e) := by
  let S := interiorCells d hclosed hsimple hreflexfree
  let R := walkRegionGraph d hclosed hsimple
  let C := innerComponent d hclosed hsimple hreflexfree
  have hcSupp : cellFace c.1 ∈ C.supp := by
    simpa [S, C] using (mem_interiorCells d hclosed hsimple hreflexfree c.1).mp c.2
  have heSupp : cellFace e.1 ∈ C.supp := by
    simpa [S, C] using (mem_interiorCells d hclosed hsimple hreflexfree e.1).mp e.2
  have hreach : R.Reachable (cellFace c.1) (cellFace e.1) :=
    C.reachable_of_mem_supp hcSupp heSupp
  obtain ⟨p⟩ := hreach
  have cellMem : ∀ (f : Site 2), f ∈ C.supp → cellFace.symm f ∈ S := by
    intro f hf
    rw [mem_interiorCells]
    rw [cellFace.apply_symm_apply]
    exact hf
  have lift : ∀ {f g : Site 2} (q : R.Walk f g) (hf : f ∈ C.supp) (hg : g ∈ C.supp),
      (cellSkeleton S).Reachable
        (skeletonRepresentative S ⟨cellFace.symm f, cellMem f hf⟩)
        (skeletonRepresentative S ⟨cellFace.symm g, cellMem g hg⟩) := by
    intro f g q
    induction q with
    | nil => intro _ _; exact Reachable.refl _
    | @cons a b z hab q ih =>
        intro ha hz
        have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hab
        have hlat : (hypercubicLattice 2).Adj
            (cellFace (cellFace.symm a)) (cellFace (cellFace.symm b)) := by
          simpa using hab.1
        have hstep := cell_representatives_reachable_of_adj S
          (cellFace.symm a) (cellFace.symm b) (cellMem a ha) (cellMem b hb) hlat
        have hstep' : (cellSkeleton S).Reachable
            (skeletonRepresentative S ⟨cellFace.symm a, cellMem a ha⟩)
            (skeletonRepresentative S ⟨cellFace.symm b, cellMem b hb⟩) := by
          simpa [skeletonRepresentative] using hstep
        exact hstep'.trans (ih hb hz)
  have h := lift p hcSupp heSupp
  simpa [S, skeletonRepresentative] using h


theorem interior_cellSkeleton_connected {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Connected := by
  let S := interiorCells d hclosed hsimple hreflexfree
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    rw [regVerts, Finset.mem_biUnion] at hu hv
    obtain ⟨c, hc, huc⟩ := hu
    obtain ⟨e, he, hve⟩ := hv
    have hucRep : (cellSkeleton S).Reachable ⟨u, hu⟩
        (skeletonRepresentative S ⟨c, hc⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S c hc u huc
    have hce := interior_representatives_reachable d hclosed hsimple hreflexfree
      (⟨c, hc⟩ : S) (⟨e, he⟩ : S)
    have hevRep : (cellSkeleton S).Reachable ⟨v, hv⟩
        (skeletonRepresentative S ⟨e, he⟩) := by
      simpa [S, skeletonRepresentative, skeletonVertexOfCorner] using
        corner_reachable_lowerLeft S e he v hve
    exact hucRep.trans (hce.trans hevRep.symm)
  · let k : Fin (m + 3) := 0
    have hc : leftCell d k ∈ S :=
      leftCell_mem_interiorCells d hclosed hsimple hreflexfree k
    exact ⟨skeletonRepresentative S ⟨leftCell d k, hc⟩⟩

theorem eulerChar_interiorCells_le_one {m : ℕ}
    (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    eulerChar (interiorCells d hclosed hsimple hreflexfree) ≤ 1 :=
  eulerChar_le_one_of_skeleton_connected _
    (interior_cellSkeleton_connected d hclosed hsimple hreflexfree)

end StatMech.Onsager.CellEulerFaithful
