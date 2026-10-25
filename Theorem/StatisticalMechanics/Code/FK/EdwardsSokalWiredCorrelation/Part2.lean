/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Def.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem esWiredPottsCenteredOnePoint_eq_conn
    (q : Nat) [NeZero q] (b : Fin q) (p : Real) (x v0 : V)
    (hv0 : bdry v0) :
    esWiredPottsCenteredOnePoint G bdry q b p x =
      ((q : Real) - 1) * wiredConnToBdryProbQ G bdry q p x := by
  classical
  unfold esWiredPottsCenteredOnePoint wiredConnToBdryProbQ
  have hk : ∀ omega : ConfigSpace (Sym2 V),
      1 ≤ numClustersBC G (boundaryCliqueGraph bdry) omega :=
    fun omega => one_le_numClustersBC G bdry v0 omega
  have hnum : (q : Real) *
      (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x)) =
      ((q : Real) - 1) *
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) := by
    rw [Finset.mul_sum]
    have hterm : ∀ omega : ConfigSpace (Sym2 V),
        (q : Real) * (∑ sigma : V → Fin q,
          esWeightWired G bdry b p sigma omega *
            pottsBoundaryObservable q b (sigma x)) =
        if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega
        else 0 := by
      intro omega
      rw [esWeightWired_pottsBoundary_sum G bdry b p omega v0 hv0 x]
      by_cases hconn : ConnToBdry G bdry omega x
      · rw [if_pos hconn, if_pos hconn]
        have hweight := esWeightWired_sum_spins_eq_bcWeight
          G bdry b p omega v0 hv0 (hk omega)
        rw [esWeightWired_sum_spins] at hweight
        have hcard :
            ((Finset.univ.filter (fun sigma : V → Fin q =>
              ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma)).card : Real) =
              (q : Real) ^
                (numClustersBC G (boundaryCliqueGraph bdry) omega - 1) := by
          have hN := card_constOnOpen_boundaryFixed G bdry b omega v0 hv0
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hN
          rw [hN]
          push_cast
          rfl
        rw [hcard] at hweight
        nlinarith
      · rw [if_neg hconn, if_neg hconn, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun omega _ => hterm omega)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x)]
    have hzero : (∑ omega ∈ Finset.univ.filter
        (fun omega : ConfigSpace (Sym2 V) => ¬ ConnToBdry G bdry omega x),
        (if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega
        else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [if_neg (Finset.mem_filter.1 homega).2]
    rw [hzero, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro omega homega
    rw [if_pos (Finset.mem_filter.1 homega).2]
  have hden : (q : Real) * esZWired G bdry q b p =
      bcZ G (boundaryCliqueGraph bdry) p (q : Real) :=
    esZWired_eq_bcZ G bdry b p v0 hv0 hk
  have hq : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [show (∑ omega ∈ Finset.univ.filter
      (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
      bcProb G (boundaryCliqueGraph bdry) p (q : Real) omega) =
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) /
            bcZ G (boundaryCliqueGraph bdry) p (q : Real) by
    unfold bcProb
    rw [Finset.sum_div]]
  calc
    (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x)) /
        esZWired G bdry q b p =
      ((q : Real) * (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V → Fin q,
        esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x))) /
        ((q : Real) * esZWired G bdry q b p) :=
          (mul_div_mul_left _ _ hq).symm
    _ = (((q : Real) - 1) *
        (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega)) /
        bcZ G (boundaryCliqueGraph bdry) p (q : Real) := by rw [hnum, hden]
    _ = ((q : Real) - 1) *
        ((∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x),
          bcWeight G (boundaryCliqueGraph bdry) p (q : Real) omega) /
        bcZ G (boundaryCliqueGraph bdry) p (q : Real)) := by ring


end IsingFK
end StatMech
