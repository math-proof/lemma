/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Def.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part3
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem esWiredPottsCenteredOnePoint_eq_potts
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x : V) :
    esWiredPottsCenteredOnePoint G bdry q b
        (1 - Real.exp (-(beta * J))) x =
      ∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          pottsBoundaryObservable q b (sigma x) := by
  classical
  unfold esWiredPottsCenteredOnePoint
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [← esWiredFirstMarginal_eq_pottsProbWired G bdry b beta J sigma]
  unfold esWiredFirstMarginal
  rw [← Finset.sum_mul]
  ring

theorem pottsBoundaryObservable_expectation
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x : V) :
    (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          pottsBoundaryObservable q b (sigma x)) =
      (q : Real) * pottsBoundaryProbWired G bdry q b beta J x - 1 := by
  classical
  unfold pottsBoundaryObservable pottsBoundaryProbWired
  calc
    ∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          ((q : Real) * (if sigma x = b then 1 else 0) - 1) =
      ∑ sigma : V → Fin q,
        ((q : Real) * (pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) -
            pottsProbWired G bdry q b beta J sigma) := by
      apply Finset.sum_congr rfl
      intro sigma _
      ring
    _ = (q : Real) * (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) -
        ∑ sigma : V → Fin q, pottsProbWired G bdry q b beta J sigma := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (q : Real) * (∑ sigma : V → Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = b then 1 else 0)) - 1 := by
      rw [pottsProbWired_sum_eq_one]


theorem pottsBoundaryProbWired_sub_inv_eq_conn
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x v0 : V)
    (hv0 : bdry v0) :
    pottsBoundaryProbWired G bdry q b beta J x - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        wiredConnToBdryProbQ G bdry q
          (1 - Real.exp (-(beta * J))) x := by
  have hcenter := (esWiredPottsCenteredOnePoint_eq_potts
    G bdry q b beta J x).symm.trans
      (esWiredPottsCenteredOnePoint_eq_conn G bdry q b
        (1 - Real.exp (-(beta * J))) x v0 hv0)
  rw [pottsBoundaryObservable_expectation G bdry q b beta J x] at hcenter
  have hq : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp
  nlinarith

theorem wiredConnToBdryProbQ_eq_wiredFkProb_sum
    (q : Nat) (p : Real) (x : V) :
    wiredConnToBdryProbQ G bdry q p x =
      ∑ omega ∈ Finset.univ.filter
        (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
        wiredFkProb G bdry p (q : Real) omega := by
  unfold wiredConnToBdryProbQ
  exact Finset.sum_congr rfl (fun omega _ =>
    (wiredFkProb_eq_bcProb G bdry p (q : Real) omega).symm)


end IsingFK
end StatMech
