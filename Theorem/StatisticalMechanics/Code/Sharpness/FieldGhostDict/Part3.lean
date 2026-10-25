/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part3
open Finset SimpleGraph
open scoped symmDiff
open StatMech StatMech.Ising StatMech.Sharpness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem flipV_apply (s : ConfigSpace V) (v : V) : flipV s v = ! s v := rfl


theorem spin_flipV (s : ConfigSpace V) (v : V) : spin (flipV s) v = - spin s v := by
  simp only [flipV, spin]; by_cases h : s v <;> simp [h]


theorem bond_flipV (s : ConfigSpace V) (e : Sym2 V) : bond (flipV s) e = bond s e := by
  induction e with | h x y => rw [bond_mk, bond_mk, spin_flipV, spin_flipV]; ring


theorem flipV_involutive : Function.Involutive (flipV (V := V)) := by
  intro s; ext v; simp [flipV]


theorem isingWeight_flip (β h : ℝ) (s : ConfigSpace V) :
    isingWeight G β (-h) (flipV s) = isingWeight G β h s := by
  unfold isingWeight hamiltonian
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) = ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ => bond_flipV s e)
  have hs : (∑ x, spin (flipV s) x) = - ∑ x, spin s x := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun x _ => spin_flipV s x)
  rw [hb, hs]; ring


theorem fgd_isingZ_neg (β h : ℝ) : isingZ G β (-h) = isingZ G β h := by
  unfold isingZ
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  exact Finset.sum_congr rfl (fun s _ => isingWeight_flip G β h s)


theorem spinProd_flipV (A : Finset V) (s : ConfigSpace V) :
    spinProd A (flipV s) = (-1) ^ A.card * spinProd A s := by
  unfold spinProd
  rw [Finset.prod_congr rfl (fun x _ => spin_flipV s x)]
  rw [Finset.prod_congr rfl (fun x _ => (neg_one_mul (spin s x)).symm)]
  rw [Finset.prod_mul_distrib, Finset.prod_const]


theorem spinProd_flipV_even (A : Finset V) (hA : Even A.card) (s : ConfigSpace V) :
    spinProd A (flipV s) = spinProd A s := by
  rw [spinProd_flipV, hA.neg_one_pow, one_mul]


theorem spinProd_flipV_odd (A : Finset V) (hA : Odd A.card) (s : ConfigSpace V) :
    spinProd A (flipV s) = -spinProd A s := by
  rw [spinProd_flipV, hA.neg_one_pow, neg_one_mul]


theorem fgd_num_neg_even (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s)
      = ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_even A hA, isingWeight_flip]


theorem fgd_num_neg_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s)
      = -∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_odd A hA, isingWeight_flip]
  ring


end FieldGhostDict
end Sharpness
end StatMech
