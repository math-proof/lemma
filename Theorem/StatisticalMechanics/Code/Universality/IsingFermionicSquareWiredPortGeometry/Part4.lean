/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareMedialVertex_eq_of_oriented_tail_axis
    (n : Nat) (e f : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis =
      (fkIsingSquareOrientedEdge n f).axis)
    (htail : (fkIsingSquareOrientedEdge n e).tail =
      (fkIsingSquareOrientedEdge n f).tail) :
    e = f := by
  let a := fkIsingSquareOrientedEdge n e
  let b := fkIsingSquareOrientedEdge n f
  have haStep := a.step
  have hbStep := b.step
  have hhead : a.head = b.head := by
    apply Subtype.ext
    cases ha : a.axis <;> cases hb : b.axis
    · simp only [ha] at haStep
      simp only [hb] at hbStep
      rw [haStep, hbStep, htail]
    · simp [a, b, ha, hb] at haxis
    · simp [a, b, ha, hb] at haxis
    · simp only [ha] at haStep
      simp only [hb] at hbStep
      rw [haStep, hbStep, htail]
  apply Subtype.ext
  calc
    e.1 = s(a.tail, a.head) := a.edge_eq.symm
    _ = s(b.tail, b.head) := by rw [htail, hhead]
    _ = f.1 := b.edge_eq


theorem fkIsingSquareWiredPortIntPosition_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredPortIntPosition n) := by
  intro d f hpos
  rcases d with ⟨e, side⟩
  rcases f with ⟨f, side'⟩
  let a := fkIsingSquareOrientedEdge n e
  let b := fkIsingSquareOrientedEdge n f
  have hx := congrArg Prod.fst hpos
  have hy := congrArg Prod.snd hpos
  cases ha : a.axis <;> cases hb : b.axis <;>
    cases side <;> cases side' <;>
    simp [fkIsingSquareWiredPortIntPosition, a, b, ha, hb] at hx hy
  all_goals try omega
  all_goals
    have htail0 : a.tail.1 0 = b.tail.1 0 := by omega
    have htail1 : a.tail.1 1 = b.tail.1 1 := by omega
    have htail : a.tail = b.tail := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact htail0
      · exact htail1
    have haxis : a.axis = b.axis := ha.trans hb.symm
    have hef : e = f :=
      fkIsingSquareMedialVertex_eq_of_oriented_tail_axis n e f haxis htail
    subst f
    rfl


theorem fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    ∃ a : Fin 4,
      fkIsingSquareWiredPortIntPosition n
          (FKIsingMedialDart.localMate omega d) =
        fkIsingSquareWiredPortIntPosition n d +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases d with ⟨e, side⟩
  let a : Fin 4 := match omega e.1, side with
    | false, .west => 2
    | false, .south => 1
    | false, .east => 1
    | false, .north => 2
    | true, .west => 3
    | true, .south => 3
    | true, .east => 0
    | true, .north => 0
  refine ⟨a, ?_⟩
  cases homega : omega e.1 <;> cases side <;>
    simp only [FKIsingMedialDart.localMate, homega] <;>
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [a, homega, fkIsingSquareWiredPortIntPosition, haxis,
      fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] <;> omega


end
end StatMech.Universality
