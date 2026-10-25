/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredLiftSite_injective
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) :
    Function.Injective
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S) := by
  intro x y hxy
  have hdev : fkRectSquareDevelopPoint
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x) =
    fkRectSquareDevelopPoint
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S y) :=
    fkRectSquareSiteOfPair_injective hxy
  have hlift := fkRectSquareDevelopPoint_injective hdev
  apply Subtype.ext
  rw [← fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x,
    ← fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y,
    hlift]

theorem fkRectHorizontalCylinderUnexploredLiftPoint_step
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y) :
    fkRectHorizontalCylinderUnexploredLiftPoint R rho S y -
        fkRectHorizontalCylinderUnexploredLiftPoint R rho S x =
      fkRectDevelopedStep R x.1 y.1 := by
  let wx := fkRectHorizontalCylinderUnexploredRootWalk R rho S x
  have hroot := fkRectHorizontalCylinderUnexploredRoot_eq_of_reachable
    R rho S hxy.reachable
  let candidate :
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
        (fkRectHorizontalCylinderBottomRoots R S)).Walk
          (fkRectHorizontalCylinderUnexploredComponentRoot R rho S y) y :=
    (wx.concat hxy).copy hroot rfl
  have hdisp :=
    fkRectHorizontalCylinderUnexploredRootWalk_displacement_eq
      R rho S hno y candidate
  let inclusion := fkRectHorizontalCylinderUnexploredInclusion R rho S
  have hOne : fkRectWalkDevelopedDisplacement R
      ((SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).map inclusion) =
        fkRectDevelopedStep R x.1 y.1 := by
    simp [fkRectWalkDevelopedDisplacement, inclusion,
      fkRectHorizontalCylinderUnexploredInclusion]
  have hcandidate : fkRectWalkDevelopedDisplacement R
      (candidate.map inclusion) =
    fkRectWalkDevelopedDisplacement R (wx.map inclusion) +
      fkRectDevelopedStep R x.1 y.1 := by
    change fkRectWalkDevelopedDisplacement R
        (((wx.concat hxy).copy hroot rfl).map inclusion) = _
    rw [SimpleGraph.Walk.map_copy,
      fkRectWalkDevelopedDisplacement_copy,
      SimpleGraph.Walk.concat_eq_append,
      SimpleGraph.Walk.map_append,
      fkRectWalkDevelopedDisplacement_append]
    rw [hOne]
  rw [hcandidate] at hdisp
  unfold fkRectHorizontalCylinderUnexploredLiftPoint
  dsimp only
  have hrootPoint :
      (((fkRectHorizontalCylinderUnexploredComponentRoot R rho S y).1.1.val : Int),
        ((fkRectHorizontalCylinderUnexploredComponentRoot R rho S y).1.2.val : Int)) =
      (((fkRectHorizontalCylinderUnexploredComponentRoot R rho S x).1.1.val : Int),
        ((fkRectHorizontalCylinderUnexploredComponentRoot R rho S x).1.2.val : Int)) := by
    rw [← hroot]
  rw [hrootPoint, hdisp]
  apply Prod.ext
  · simp only [Prod.fst_sub, Prod.fst_add]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add]
    ring

theorem fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y) :
    (hypercubicLattice 2).Adj
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S x)
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S y) := by
  have hcyl : (fkRectHorizontalCylinderGraph R).Adj x.1 y.1 := hxy
  have htorus := (fkRectHorizontalCylinderGraph_adj_iff R x.1 y.1).mp hcyl |>.1
  let px := fkRectHorizontalCylinderUnexploredLiftPoint R rho S x
  have hpx : fkRectLiftedVertex R px = x.1 :=
    fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x
  obtain ⟨q, hq, hqstep, haxis⟩ :=
    fkRectTorusGraph_adj_squareLift R htorus px hpx
  have hstep := fkRectHorizontalCylinderUnexploredLiftPoint_step
    R rho S hno hxy
  have hqEq : q =
      fkRectHorizontalCylinderUnexploredLiftPoint R rho S y := by
    dsimp [px] at hqstep
    apply Prod.ext
    · have h1 := congrArg Prod.fst hqstep
      have h2 := congrArg Prod.fst hstep
      simp only [Prod.fst_sub] at h1 h2 ⊢
      omega
    · have h1 := congrArg Prod.snd hqstep
      have h2 := congrArg Prod.snd hstep
      simp only [Prod.snd_sub] at h1 h2 ⊢
      omega
  rw [hqEq] at haxis
  exact (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mp haxis

theorem fkRectIntModFin_sub_one
    {N : Nat} (hN : 0 < N) (z : Int) :
    fkRectIntModFin hN (z - 1) =
      SixVertexArrows.cyclicPred hN (fkRectIntModFin hN z) := by
  apply Fin.ext
  rw [fkRectCyclicPred_val]
  let r := z % (N : Int)
  have hN0 : (N : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hr0 : 0 ≤ r := Int.emod_nonneg z hN0
  have hrN : r < (N : Int) := by
    simpa using Int.emod_lt z hN0
  have hzmod : (z - 1) % (N : Int) = (r - 1) % (N : Int) := by
    rw [Int.sub_emod]
    simp [r]
  by_cases hr : r = 0
  · have hrepr : (r - 1) = ((N - 1 : Nat) : Int) + (N : Int) * (-1) := by
      rw [hr]
      omega
    have hnonneg : (0 : Int) ≤ ((N - 1 : Nat) : Int) := by omega
    have hlt : ((N - 1 : Nat) : Int) < N := by omega
    have hmod : (z - 1) % (N : Int) = (N - 1 : Nat) := by
      rw [hzmod, hrepr, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt hnonneg hlt]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod]
    rw [hmod, Int.toNat_natCast]
    have hval : (z % (N : Int)).toNat = 0 := by
      change r.toNat = 0
      rw [hr]
      rfl
    rw [hval, if_pos rfl]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hrsub0 : 0 ≤ r - 1 := by omega
    have hrsubN : r - 1 < (N : Int) := by omega
    have hmod : (z - 1) % (N : Int) = r - 1 := by
      rw [hzmod, Int.emod_eq_of_lt hrsub0 hrsubN]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod]
    rw [hmod]
    have hrnat : ((r - 1).toNat : Int) = r - 1 :=
      Int.natCast_toNat_eq_self.mpr hrsub0
    have hzNat : (((z % (N : Int)).toNat : Nat) : Int) = r := by
      rw [Int.natCast_toNat_eq_self.mpr hr0]
    have hval0 : (z % (N : Int)).toNat ≠ 0 := by
      intro hzero
      have : r = 0 := by
        rw [← hzNat]
        simp [hzero]
      exact hr this
    rw [if_neg hval0]
    omega

theorem fkRectTorusGraph_adj_of_squareDownStep_lifts
    (R : FKRectTorus) (p q : Int × Int)
    (hpRow : p.2 = ((fkRectLiftedVertex R p).2.val : Int))
    (hqRow : q.2 = ((fkRectLiftedVertex R q).2.val : Int))
    (hstep :
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) :
    (fkRectTorusGraph R).Adj
      (fkRectLiftedVertex R p) (fkRectLiftedVertex R q) := by
  let x := fkRectLiftedVertex R p
  let y := fkRectLiftedVertex R q
  have hrowRecoverP := fkRectSquareDevelopPoint_fst_sub_snd p
  have hrowRecoverQ := fkRectSquareDevelopPoint_fst_sub_snd q
  have hcolRecoverP := fkRectSquareDevelopPoint_snd_add_rowHalf p
  have hcolRecoverQ := fkRectSquareDevelopPoint_snd_add_rowHalf q
  have hrowOfStep (hs :
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
      fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) :
      q.2 = p.2 - 1 := by
    rcases hs with hs | hs <;>
      have hu := congrArg Prod.fst hs <;>
      have hv := congrArg Prod.snd hs <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hu hv <;>
      omega
  have hrow : q.2 = p.2 - 1 := hrowOfStep hstep
  have hxrow0 : x.2.val ≠ 0 := by
    intro hx0
    have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
    dsimp [x, y] at hx0 hyNonneg
    rw [hpRow, hqRow] at hrow
    simp only [hx0, Nat.cast_zero] at hrow
    omega
  have hpredRow :
      SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
    apply Fin.ext
    rw [fkRectCyclicPred_val]
    simp only [if_neg hxrow0]
    have hrowVal : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [x, y]
      rw [← hpRow, ← hqRow]
      exact hrow
    omega
  rcases hstep with hstep | hstep
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hpY : p.2 = 2 * (k : Int) := by
        have hkP : (fkRectLiftedVertex R p).2.val = k + k := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            (k : Int) + k := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) - 1 := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) - 1 := by rw [hqY]; omega
      have hcol : q.1 = p.1 - 1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos x.1 = y.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [← fkRectIntModFin_sub_one R.width_pos p.1]
        congr 1
        omega
      let e : R.EdgeIndex := (false, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
        if_false, hevenX, if_true]
      rw [hpredCol, hpredRow]
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hpY : p.2 = 2 * (k : Int) + 1 := by
        have hkP : (fkRectLiftedVertex R p).2.val = 2 * k + 1 := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            2 * (k : Int) + 1 := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) := by rw [hqY]; omega
      have hcol : q.1 = p.1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hcolFin : y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [hcol]
      let e : R.EdgeIndex := (true, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, if_true]
      rw [hpredRow]
      exact congrArg (fun z => s(x, z)) (Prod.ext hcolFin.symm rfl)
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hpY : p.2 = 2 * (k : Int) := by
        have hkP : (fkRectLiftedVertex R p).2.val = k + k := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            (k : Int) + k := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) - 1 := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) - 1 := by rw [hqY]; omega
      have hcol : q.1 = p.1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hcolFin : y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [hcol]
      let e : R.EdgeIndex := (true, x)
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, if_true]
      rw [hpredRow]
      exact congrArg (fun z => s(x, z)) (Prod.ext hcolFin.symm rfl)
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hoddX : Odd x.2.val := ⟨k, hk⟩
      have hpY : p.2 = 2 * (k : Int) + 1 := by
        have hkP : (fkRectLiftedVertex R p).2.val = 2 * k + 1 := by
          simpa [x] using hk
        have hkInt : ((fkRectLiftedVertex R p).2.val : Int) =
            2 * (k : Int) + 1 := by exact_mod_cast hkP
        rw [hpRow]
        omega
      have hqY : q.2 = 2 * (k : Int) := by omega
      have hpHalf : p.2 / 2 = (k : Int) := by rw [hpY]; omega
      have hqHalf : q.2 / 2 = (k : Int) := by rw [hqY]; omega
      have hcol : q.1 = p.1 + 1 := by
        rw [hpHalf] at hcolRecoverP
        rw [hqHalf] at hcolRecoverQ
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos y.1 = x.1 := by
        dsimp [x, y, fkRectLiftedVertex]
        rw [← fkRectIntModFin_sub_one R.width_pos q.1]
        congr 1
        omega
      let e : R.EdgeIndex := (false, (y.1, x.2))
      refine ⟨e, ?_⟩
      change fkRectTorusIndexedEdge R e = s(x, y)
      dsimp [e]
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
        if_false, heven, if_false]
      rw [hpredCol, hpredRow]

theorem fkRectHorizontalCylinderUnexplored_adj_of_liftSite_adj
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (hypercubicLattice 2).Adj
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S x)
      (fkRectHorizontalCylinderUnexploredLiftSite R rho S y)) :
    (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Adj x y := by
  let px := fkRectHorizontalCylinderUnexploredLiftPoint R rho S x
  let py := fkRectHorizontalCylinderUnexploredLiftPoint R rho S y
  have haxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint px) (fkRectSquareDevelopPoint py) :=
    (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mpr hxy
  have hpxRow : px.2 = ((fkRectLiftedVertex R px).2.val : Int) := by
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x]
    exact fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val R rho S x
  have hpyRow : py.2 = ((fkRectLiftedVertex R py).2.val : Int) := by
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y]
    exact fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val R rho S y
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectLiftedVertex R px) (fkRectLiftedVertex R py) := by
    rcases haxis with h | h | h | h
    · exact fkRectTorusGraph_adj_of_squareDownStep_lifts
        R px py hpxRow hpyRow (Or.inl h)
    · exact fkRectTorusGraph_adj_of_squareDownStep_lifts
        R px py hpxRow hpyRow (Or.inr h)
    · apply (fkRectTorusGraph R).symm
      apply fkRectTorusGraph_adj_of_squareDownStep_lifts
        R py px hpyRow hpxRow
      left
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' ⊢ <;>
        omega
    · apply (fkRectTorusGraph R).symm
      apply fkRectTorusGraph_adj_of_squareDownStep_lifts
        R py px hpyRow hpxRow
      right
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' ⊢ <;>
        omega
  have hrowDiff :
      (((fkRectLiftedVertex R py).2.val : Int) -
        (fkRectLiftedVertex R px).2.val).natAbs = 1 := by
    have hpRecover := fkRectSquareDevelopPoint_fst_sub_snd px
    have hqRecover := fkRectSquareDevelopPoint_fst_sub_snd py
    rw [hpxRow] at hpRecover
    rw [hpyRow] at hqRecover
    rcases haxis with h | h | h | h <;>
      have h' := congrArg Prod.fst h <;>
      have h'' := congrArg Prod.snd h <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at h' h'' <;>
      omega
  have hnotSeam : ¬ fkRectCrossesVerticalSeam R
      s(fkRectLiftedVertex R px, fkRectLiftedVertex R py) := by
    rw [fkRectCrossesVerticalSeam_mk]
    intro hcross
    have hh := R.height_gt_two
    rcases hcross with ⟨hx0, hylast⟩ | ⟨hy0, hxlast⟩ <;>
      omega
  apply (fkRectHorizontalCylinderGraph_adj_iff R x.1 y.1).mpr
  refine ⟨?_, ?_⟩
  · simpa [px, py,
      fkRectHorizontalCylinderUnexploredLiftPoint_project] using htorus
  · intro hcut
    rw [fkRectHorizontalCutGraphEdges, Finset.mem_image] at hcut
    obtain ⟨a, ha, hea⟩ := hcut
    apply hnotSeam
    have hpair : s(fkRectLiftedVertex R px, fkRectLiftedVertex R py) =
        s(x.1, y.1) := by
      rw [fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x,
        fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S y]
    rw [hpair, ← hea]
    exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut_planarization
      R a ha


end
end StatMech.FrontierD
