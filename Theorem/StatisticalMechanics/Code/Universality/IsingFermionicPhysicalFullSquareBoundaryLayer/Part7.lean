/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part7


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  unfold fkIsingSquareBoundaryLayerFirstFaceTrace
  ring

theorem fkIsingSquareBoundaryLayer_vertex_le_firstFaceTrace
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareBoundaryVertex n (side, k)) <=
      fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k := by
  rw [<- sub_nonneg]
  rw [fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex]
  exact fkIsingSquareBoundaryLayerInwardIncrement_nonneg n hn side k


theorem fkIsingSquareBoundaryLayer_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  rw [fkIsingSquareBoundaryLayerVertexFermion_normSq,
    fkIsingSquareBoundaryLayerInwardIncrement]
  rw [<- mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]


theorem fkIsingSquareBoundaryLayer_fermionicSummand_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.bond d) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.dart d) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  by_cases hd : (.dart d : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega
  · have hpair := fkIsingSquareWired_incidence_infix_explorationOrder
      n hn omega' d (by simpa [D, omega',
        fkIsingSquareBoundaryRestrictedDobrushinDomain] using hd)
    have hb : (.bond d : FKIsingSquareWiredCarrier n) ∈
        D.exploration omega := by
      change (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      exact hpair.elim (fun h => h.mem (by simp))
        (fun h => h.mem (by simp))
    have hwind := fkIsingSquareWiredLiftedWinding_incidence
      n hn omega' d (by simpa [D, omega',
        fkIsingSquareBoundaryRestrictedDobrushinDomain] using hd)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hd, if_pos hb]
    unfold FKIsingDobrushinDomain.windingPhase
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d)) / 2 :
            Real) : Complex)) = _
    rw [hwind]
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.dart d)) / 2 :
            Real) : Complex)) =
      (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.dart d)) / 2 :
            Real) : Complex))
    rfl
  · have hb : (.bond d : FKIsingSquareWiredCarrier n) ∉
        D.exploration omega := by
      intro hbond
      have htrace : (.bond d : FKIsingSquareWiredCarrier n) ∈
          fkIsingSquareWiredExplorationTrace n hn omega' := by
        rw [mem_fkIsingSquareWiredExplorationTrace_iff]
        rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hbond
      have hdtrace :=
        (fkIsingSquareWired_incidence_mem_trace_iff n hn omega' d).1 htrace
      apply hd
      change (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hdtrace
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_neg hd, if_neg hb]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_incidence
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.bond d) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d) := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_incidence
    n hn omega d


theorem fkIsingSquareBoundaryLayer_fermionicSummand_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
          omega (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  have hmem := fkIsingSquareWired_bondMate_mem_trace_iff
    n hn omega' d hsource hterminal
  by_cases hd : (.bond d : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega
  · have hdtrace : (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega' := by
      rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
        using hd
    have hftrace := hmem.mpr hdtrace
    have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∈ D.exploration omega := by
      change _ ∈ fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hftrace
    have hwind := fkIsingSquareWiredLiftedWinding_bondMate
      n hn omega' d hsource hterminal (by
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hd)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hd, if_pos hf]
    unfold FKIsingDobrushinDomain.windingPhase
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega'
            (.bond (fkIsingSquareWiredBondMate n hn d))) / 2 : Real) :
              Complex)) = _
    rw [hwind]
    unfold fkIsingSquareWiredBondPhase
    rw [show Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d) +
              (fkIsingSquareWiredBondTurn n hn d
                (fkIsingSquareWiredBondMate n hn d) : Real) *
                  (Real.pi / 4)) / 2 : Real) : Complex) =
        Complex.I *
            ((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d) / 2 :
              Real) : Complex) +
          Complex.I *
            ((((fkIsingSquareWiredBondTurn n hn d
              (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
                (Real.pi / 8) : Real) : Complex) by push_cast; ring,
      Complex.exp_add]
    change (D.criticalMass omega : Complex) * (_ * _) =
      (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d)) / 2 :
            Real) : Complex)) * _
    ring
  · have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∉ D.exploration omega := by
      intro hmate
      have hftrace : (.bond (fkIsingSquareWiredBondMate n hn d) :
          FKIsingSquareWiredCarrier n) ∈
          fkIsingSquareWiredExplorationTrace n hn omega' := by
        rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hmate
      apply hd
      change (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hmem.mp hftrace
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_neg hd, if_neg hf, zero_mul]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_bondMate
    n hn omega d hsource hterminal

theorem fkIsingSquareBoundaryLayer_eq_of_sameCycle_of_step
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (f : A -> B)
    (hstep : forall x, f (sigma x) = f x) {x y : A}
    (hxy : sigma.SameCycle x y) : f x = f y := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  have hpow : forall m : Nat, f ((sigma ^ m) x) = f x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep]
        exact ih
  calc
    f x = f ((sigma ^ k) x) := (hpow k).symm
    _ = f y := congrArg f hk


end
end StatMech.Universality
