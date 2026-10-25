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
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredLiftPoint_project
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    fkRectLiftedVertex R
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x) = x.1 := by
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  let w := (fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
    (fkRectHorizontalCylinderUnexploredInclusion R rho S)
  have hp : fkRectLiftedVertex R p = root.1 := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  obtain ⟨q, hq⟩ := fkRectWalk_exists_squareLift R hsub w p hp
  have hdisp := hq.sub_eq_developedDisplacement R
  have hqEq : q = p + fkRectWalkDevelopedDisplacement R w := by
    apply Prod.ext
    · have h := congrArg Prod.fst hdisp
      simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
      omega
    · have h := congrArg Prod.snd hdisp
      simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
      omega
  change fkRectLiftedVertex R
      (p + fkRectWalkDevelopedDisplacement R w) = x.1
  rw [← hqEq]
  exact hq.end_project R

theorem fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S) :
    (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x).2 =
      (x.1.2.val : Int) := by
  let root := fkRectHorizontalCylinderUnexploredComponentRoot R rho S x
  let p : Int × Int := ((root.1.1.val : Int), (root.1.2.val : Int))
  let w := (fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
    (fkRectHorizontalCylinderUnexploredInclusion R rho S)
  have hp : fkRectLiftedVertex R p = root.1 := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have hsub : fkRectHorizontalCylinderGraph R ≤ fkRectTorusGraph R := by
    intro a b hab
    exact (fkRectHorizontalCylinderGraph_adj_iff R a b).mp hab |>.1
  obtain ⟨q, hq⟩ := fkRectWalk_exists_squareLift R hsub w p hp
  have hdisp := hq.sub_eq_developedDisplacement R
  have hqEq : q = p + fkRectWalkDevelopedDisplacement R w := by
    apply Prod.ext
    · have h := congrArg Prod.fst hdisp
      simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
      omega
    · have h := congrArg Prod.snd hdisp
      simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
      omega
  have hqRow : q.2 = (x.1.2.val : Int) :=
    hq.end_snd_eq_val_of_cylinder R rfl
  change (p + fkRectWalkDevelopedDisplacement R w).2 =
    (x.1.2.val : Int)
  rw [← hqEq]
  exact hqRow

theorem fkRectHorizontalCylinderUnexploredRoot_eq_of_reachable
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
    (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Reachable x y) :
    fkRectHorizontalCylinderUnexploredComponentRoot R rho S x =
      fkRectHorizontalCylinderUnexploredComponentRoot R rho S y := by
  apply congrArg Quot.out
  exact SimpleGraph.ConnectedComponent.sound hxy

theorem fkRectHorizontalCylinderUnexploredRootWalk_displacement_eq
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
    (x : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (w : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk
        (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) x) :
    fkRectWalkDevelopedDisplacement R
        ((fkRectHorizontalCylinderUnexploredRootWalk R rho S x).map
          (fkRectHorizontalCylinderUnexploredInclusion R rho S)) =
      fkRectWalkDevelopedDisplacement R
        (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) := by
  let chosen := fkRectHorizontalCylinderUnexploredRootWalk R rho S x
  let c := chosen.append w.reverse
  have hcFst := hno _ c
  have hcSnd :=
    fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero
      R rho S c
  have hwindChosen : fkRectWalkWinding R
      (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) =
    fkRectWalkWinding R
      (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) := by
    apply Prod.ext
    · change (fkRectWalkWinding R
          (c.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 = 0
        at hcFst
      simp only [c, SimpleGraph.Walk.map_append] at hcFst
      rw [← SimpleGraph.Walk.reverse_map,
        fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hcFst
      change (fkRectWalkWinding R
          (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 +
        -(fkRectWalkWinding R
          (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).1 = 0
        at hcFst
      omega
    · change (fkRectWalkWinding R
          (c.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 = 0
        at hcSnd
      simp only [c, SimpleGraph.Walk.map_append] at hcSnd
      rw [← SimpleGraph.Walk.reverse_map,
        fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hcSnd
      change (fkRectWalkWinding R
          (chosen.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 +
        -(fkRectWalkWinding R
          (w.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))).2 = 0
        at hcSnd
      omega
  rw [fkRectWalkDevelopedDisplacement_eq,
    fkRectWalkDevelopedDisplacement_eq, hwindChosen]


end
end StatMech.FrontierD
