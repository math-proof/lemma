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
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {bottomX : Fin R.width}
    (hbottomS : bottomX ∈ S)
    (hcross : FKRectHorizontalCylinderCrossingSource R rho bottomX) :
    FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
  obtain ⟨topX, hreach⟩ := hcross
  obtain ⟨Vopen⟩ := hreach
  let inclusion : FK.openSub (fkRectHorizontalCylinderGraph R) rho →g
      fkRectHorizontalCylinderGraph R :=
    { toFun := id
      map_rel' := by
        intro a b h
        exact (FK.openSub_le (fkRectHorizontalCylinderGraph R) rho) h }
  let V := Vopen.map inclusion
  intro x p hwind
  obtain ⟨v, hvp, hvV⟩ :=
    fkRectHorizontalCylinder_support_intersects_bottomTop
      R bottomX topX V p hwind
  refine ⟨v, hvp, ?_⟩
  rw [fkRectHorizontalCylinderExploredVertex_iff]
  refine ⟨bottomX, hbottomS, ?_⟩
  have hvOpen : v ∈ Vopen.support := by
    change v ∈ (Vopen.map inclusion).support at hvV
    rw [SimpleGraph.Walk.support_map] at hvV
    obtain ⟨z, hz, hzv⟩ := List.mem_map.mp hvV
    simpa [inclusion] using hzv ▸ hz
  exact (Vopen.takeUntil v hvOpen).reachable


theorem fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
  obtain ⟨x, hx⟩ := hS
  apply fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot
    R rho S hx
  exact ⟨pair x, hW.1 x hx⟩

theorem fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width)) {x y}
    (p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
      (fkRectHorizontalCylinderBottomRoots R S)).Walk x y) :
    (fkRectHorizontalCylinderUnexploredWalkWinding R rho S p).2 = 0 := by
  exact fkRectHorizontalCylinderWalk_winding_snd_eq_zero R
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S))


theorem fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (hsep : FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding
      R rho S) :
    FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
  intro x p
  by_contra hwind
  obtain ⟨v, hvp, hvExplored⟩ := hsep
    (p.map (fkRectHorizontalCylinderUnexploredInclusion R rho S)) hwind
  rw [SimpleGraph.Walk.support_map] at hvp
  obtain ⟨v', hv'p, hv'v⟩ := List.mem_map.mp hvp
  have hvUnexplored :
      ¬ FKRectHorizontalCylinderExploredVertex R rho S v'.1 := v'.2
  apply hvUnexplored
  have hvEq : v'.1 = v := by
    simpa [fkRectHorizontalCylinderUnexploredInclusion] using hv'v
  exact hvEq.symm ▸ hvExplored


theorem fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width))
    (hS : S.Nonempty)
    (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
    FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
  apply fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation
  exact fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness
    R rho pair S hS hW

theorem fkRectWalkDevelopedDisplacement_append
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x y z : R.Vertex}
    (p : G.Walk x y) (q : G.Walk y z) :
    fkRectWalkDevelopedDisplacement R (p.append q) =
      fkRectWalkDevelopedDisplacement R p +
        fkRectWalkDevelopedDisplacement R q := by
  induction p with
  | nil => simp [fkRectWalkDevelopedDisplacement]
  | @cons a b c hab p ih =>
      simp only [SimpleGraph.Walk.cons_append,
        fkRectWalkDevelopedDisplacement]
      rw [ih]
      apply Prod.ext <;> simp <;> ring

theorem fkRectWalkDevelopedDisplacement_reverse
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x y : R.Vertex}
    (p : G.Walk x y) :
    fkRectWalkDevelopedDisplacement R p.reverse =
      -fkRectWalkDevelopedDisplacement R p := by
  induction p with
  | nil => simp [fkRectWalkDevelopedDisplacement]
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.reverse_cons,
        fkRectWalkDevelopedDisplacement_append, ih]
      simp only [fkRectWalkDevelopedDisplacement, neg_add_rev]
      rw [fkRectDevelopedStep_swap]
      simp

theorem fkRectWalkDevelopedDisplacement_copy
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y x' y' : R.Vertex} (p : G.Walk x y)
    (hx : x = x') (hy : y = y') :
    fkRectWalkDevelopedDisplacement R (p.copy hx hy) =
      fkRectWalkDevelopedDisplacement R p := by
  subst x'
  subst y'
  rfl


end
end StatMech.FrontierD
