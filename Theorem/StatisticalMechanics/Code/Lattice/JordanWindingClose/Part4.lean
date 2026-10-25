/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part7
import Def.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwc_whbSync_of_keepResidue (P : PlanarZ2Subgraph) (hkeep : jwc_KeepResidue P) :
    jfc_WhbSync P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared
  constructor
  · intro hreach
    exact jwc_syncMerge P K hKle hadjG hnotK hfg hshared hreach
  · intro hsep
    by_contra hnr
    exact hsep (hkeep K hKle hadjG hnotK hfg hshared hnr)


theorem jwc_faithfulDiscreteJordan_of_keepResidue (P : PlanarZ2Subgraph)
    (hkeep : jwc_KeepResidue P) : whc_FaithfulDiscreteJordan P :=
  jfc_faithfulDiscreteJordan_of_sync P (jwc_whbSync_of_keepResidue P hkeep)


theorem jwc_square_edgeFlip_closedEven :
    wcl_ClosedEven (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset) := by
  classical
  apply (jwc_edgeFlip_closedEven_iff_closedContour _).mpr
  rw [Set.coe_toFinset]
  exact jeb_square_closedContour


theorem jwc_square_vertexLoop_even (c d : ℤ) :
    Even (wcl_flipCount (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset)
      (jwc_vertexLoop c d)) := by
  classical
  rw [jwc_vertexLoop_even_iff]
  have := (jwc_edgeFlip_closedEven_iff_closedContour
    ((imageGraph jbc_Pce).edgeSet.toFinset)).mp jwc_square_edgeFlip_closedEven
  have h := this ![c, d]
  simpa using h


theorem jwc_keep_of_freeHead (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {x y : P.V} (hadjG : P.G.Adj x y) (hfree : ∀ w, ¬ (jei_pushGraph P K).Adj (P.emb x) w)
    {f0 g0 : Site 2} (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
    ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  have hlatpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  obtain ⟨f0', g0', hfg', hshared', hreach'⟩ :=
    jic_dangling_bridge (jei_pushGraph P K) hfree hlatpq.symm
  
  have hedgeEq : s(f0, g0) = s(f0', g0') := by
    apply (jce_sharedPrimalEdge_inj hfg hfg').mpr
    rw [hshared, hshared', Sym2.eq_swap]
  rw [hedgeEq]
  
  have : ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0', g0')}).Reachable f0' g0' := hreach'
  
  rw [Sym2.eq_iff] at hedgeEq
  rcases hedgeEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hreach'
  · exact hreach'.symm


theorem jwc_summary :
    (∀ (H : SimpleGraph (Site 2)) [Fintype H.edgeSet] (f0 g0 : Site 2),
        (hypercubicLattice 2).Adj f0 g0 →
        (wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔
          jce_ClosedContour
            ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
              : Set (Sym2 (Site 2))))) ∧
      (∀ (P : PlanarZ2Subgraph), jwc_KeepResidue P → whc_FaithfulDiscreteJordan P) ∧
      (∀ (P : PlanarZ2Subgraph), jcx_IsEvenPeelable P.G → whc_FaithfulDiscreteJordan P) :=
  ⟨fun H _ f0 g0 hfg => jwc_cutFlip_closedEven_iff_closedContour H f0 g0 hfg,
    jwc_faithfulDiscreteJordan_of_keepResidue,
    jwc_faithfulDiscreteJordan_of_evenPeelable⟩

end Lattice
end StatMech
