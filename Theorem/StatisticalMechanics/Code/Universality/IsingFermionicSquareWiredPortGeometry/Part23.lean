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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part24


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpandedDartStepIndex_spec
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart) :
    fkIsingSquareWiredExpandedIntPosition n hn d.snd =
      fkIsingSquareWiredExpandedIntPosition n hn d.fst +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega d) :=
  Classical.choose_spec
    (fkIsingSquareWiredExpandedGraph_step n hn omega d.adj)

theorem fkIsingSquareWiredExpandedDart_vector_eq_step
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart) :
    (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.snd -
        (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.fst =
      fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega d)) := by
  change fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn d.snd) -
      fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn d.fst) = _
  rw [fkIsingSquareWiredExpandedDartStepIndex_spec]
  simp [fkIsingSquareWiredExpandedEmbedding,
    fkIsingSquareWiredIntPoint, Function.comp_apply]
  ring

theorem fkIsingSquareWiredUnitDiagonalAxis_opposite_step
    (a b : Fin 4)
    (h : fkIsingSquareWiredUnitDiagonalAxis b =
      fkIsingSquareWiredUnitDiagonalAxis a + 2) :
    fkIsingSquareWiredUnitDiagonalStep b =
      -fkIsingSquareWiredUnitDiagonalStep a := by
  fin_cases a <;> fin_cases b <;>
    simp_all [fkIsingSquareWiredUnitDiagonalAxis,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def,
      Fin.ext_iff, Prod.ext_iff]


theorem fkIsingSquareWiredExpandedCycle_step_not_opposite
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∀ k : Fin p.darts.length,
      fkIsingSquareWiredUnitDiagonalAxis
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega
            (StatMech.FrontierA.kwGraphCycleDartLoop p (k + 1))) ≠
        fkIsingSquareWiredUnitDiagonalAxis
            (fkIsingSquareWiredExpandedDartStepIndex n hn omega
              (StatMech.FrontierA.kwGraphCycleDartLoop p k)) + 2 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k hopposite
  let d := StatMech.FrontierA.kwGraphCycleDartLoop p k
  let e := StatMech.FrontierA.kwGraphCycleDartLoop p (k + 1)
  have hadj := StatMech.FrontierA.kwGraphCycleDartLoop_valid p hp k
  have hstepD := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega d
  have hstepE := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega e
  have hopen := fkIsingSquareWiredUnitDiagonalAxis_opposite_step
    (fkIsingSquareWiredExpandedDartStepIndex n hn omega d)
    (fkIsingSquareWiredExpandedDartStepIndex n hn omega e) hopposite
  have hend : e.snd = d.fst := by
    apply (fkIsingSquareWiredExpandedIntPosition_injective n hn)
    rw [hstepE, ← hadj, hstepD, hopen]
    simp
  have hedge : e.edge = d.edge := by
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨hadj.symm, hend⟩
  exact (StatMech.FrontierA.kwGraphCycleDartLoop_nonbacktracking
    (fkIsingSquareWiredExpandedGraph n hn omega) p hp k).2 hedge.symm


theorem fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
    let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
    (∑ k : Fin p.darts.length,
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop k)))
        (fkIsingSquareWiredUnitDiagonalTangentCode
          (direction (loop (k + 1))))) ≡ 8 [ZMOD 16] := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  dsimp only
  let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
  let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
  let turn : Fin p.darts.length → Int := fun k =>
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop k)))
      (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop (k + 1))))
  apply fkIsingSquareWiredExpandedCycle_turn_mod_sixteen
    n hn omega p hp (∑ k, turn k)
  have hexponent :
      ((((((∑ k, turn k) : Int) : Real) * (Real.pi / 8) : Real) : Complex) *
          Complex.I) =
        ∑ k, (((((turn k : Int) : Real) * (Real.pi / 8) : Real) : Complex) *
          Complex.I) := by
    push_cast
    simpa [mul_assoc] using
      (Finset.sum_mul Finset.univ
        (fun k => ((turn k : Int) : Complex))
        ((((Real.pi / 8 : Real) : Complex)) * Complex.I))
  rw [hexponent, Complex.exp_sum]
  unfold StatMech.FrontierA.kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  rw [← (fkIsingSquareWiredExpandedEmbedding n hn omega).vectorTurnPhase_eq_turnPhase]
  rw [fkIsingSquareWiredExpandedDart_vector_eq_step,
    fkIsingSquareWiredExpandedDart_vector_eq_step]
  exact (fkIsingSquareWiredUnitDiagonal_turnPhase _ _
    (fkIsingSquareWiredExpandedCycle_step_not_opposite n hn omega p hp k)).symm


end
end StatMech.Universality
