/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderEndpointLift
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (sourceX targetX : Fin R.width)
    (hsource : source.1 = (sourceX, fkRectBottomRow R))
    (htarget : target.1 = (targetX, fkRectTopRow R)) :
    let dx :=
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 -
        (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1
    fkRectHorizontalCylinderUnexploredLiftSite R rho S target -
        fkRectHorizontalCylinderUnexploredLiftSite R rho S source =
      fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
  dsimp only
  let p := fkRectHorizontalCylinderUnexploredLiftPoint R rho S source
  let q := fkRectHorizontalCylinderUnexploredLiftPoint R rho S target
  have hpRow : p.2 = 0 := by
    dsimp [p]
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val]
    rw [hsource]
    simp [fkRectBottomRow]
  have hqRow : q.2 = (R.height : Int) - 1 := by
    dsimp [q]
    rw [fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val]
    rw [htarget]
    have hh := R.height_pos
    simp [fkRectTopRow]
    omega
  obtain ⟨k, hk⟩ := R.height_even
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderUnexploredLiftSite,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectSquareDevelopPoint, p, q, hpRow, hqRow, hk] <;>
    omega


theorem FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness_embedding_sub
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width -> Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    (sourceX targetX : Fin R.width)
    (hsource : source.1 = (sourceX, fkRectBottomRow R))
    (htarget : target.1 = (targetX, fkRectTopRow R)) :
    let dx :=
      (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 -
        (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1
    ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R rho pair S hS hW).embedding target).1 -
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R rho pair S hS hW).embedding source).1 =
      fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
  exact fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub
    R rho S source target sourceX targetX hsource htarget


theorem fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub
    (R : FKRectTorus) (dx : Int) :
    (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 0 -
        (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 1 =
      (R.height : Int) - 1 := by
  obtain ⟨k, hk⟩ := R.height_even
  simp [fkRectHorizontalCylinderSquareLiftedDisplacement, hk]
  omega


theorem fkRectHorizontalCylinder_oldDisplacement_parameter_eq
    (R : FKRectTorus) (rawDx oldDx : Int)
    (hbad : fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height =
      fkRectHorizontalCylinderLiftedDisplacement oldDx R.height) :
    oldDx = 2 * ((R.height : Int) - 1) := by
  have hcoord :=
    fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub R rawDx
  rw [hbad] at hcoord
  have hzero := congrFun hbad 0
  have hone := congrFun hbad 1
  simp [fkRectHorizontalCylinderSquareLiftedDisplacement,
    fkRectHorizontalCylinderLiftedDisplacement] at hzero hone hcoord
  omega


theorem fkRectHorizontalCylinder_not_oldDisplacement_of_width_lt
    (R : FKRectTorus) (rawDx : Int)
    (htall : R.width < 2 * (R.height - 1)) :
    ¬ (∃ oldDx : Int,
      fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height =
          fkRectHorizontalCylinderLiftedDisplacement oldDx R.height ∧
        oldDx.natAbs <= R.width) := by
  rintro ⟨oldDx, hbad, hbound⟩
  have hold := fkRectHorizontalCylinder_oldDisplacement_parameter_eq
    R rawDx oldDx hbad
  have hheight : 0 <= (R.height : Int) - 1 := by
    have hh := R.height_pos
    omega
  have habs : oldDx.natAbs = 2 * (R.height - 1) := by
    rw [hold]
    have hnonneg : 0 <= 2 * ((R.height : Int) - 1) := by positivity
    apply Nat.cast_injective (R := Int)
    rw [Int.natAbs_of_nonneg hnonneg]
    push_cast
    omega
  rw [habs] at hbound
  omega


end
end StatMech.FrontierD
