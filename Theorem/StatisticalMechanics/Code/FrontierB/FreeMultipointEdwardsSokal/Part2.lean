/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part3
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esMultiPoint_eq_allClustersEvenProb (p : Real) (A : Finset V) :
    esMultiPoint G p A = allClustersEvenProb G p A := by
  classical
  unfold esMultiPoint allClustersEvenProb fkProb
  rw [Finset.sum_congr rfl
    (fun omega _ => esWeight_multipoint_spin_sum G p omega A)]
  rw [esZ_eq_fkZ, Nat.cast_ofNat, Finset.sum_div]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun omega : ConfigSpace (Sym2 V) => AllClustersEven G omega A)]
  have hzero :
      (∑ omega ∈ Finset.univ.filter (fun omega : ConfigSpace (Sym2 V) =>
          ¬ AllClustersEven G omega A),
        (if AllClustersEven G omega A then fkWeight G p (2 : Real) omega else 0) /
          fkZ G p 2) = 0 := by
    apply Finset.sum_eq_zero
    intro omega homega
    rw [if_neg (Finset.mem_filter.mp homega).2, zero_div]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [if_pos (Finset.mem_filter.mp homega).2]

omit [Fintype V] [DecidableEq V] in
theorem isingSpin_eq_neg_spin_toIsing (sigma : V -> Fin 2) (x : V) :
    isingSpin (sigma x) = -Ising.spin (IsingFK.toIsing sigma) x := by
  generalize ha : sigma x = a
  fin_cases a <;>
    simp only [isingSpin, Ising.spin, IsingFK.toIsing, ha,
      finTwoEquiv, Equiv.coe_fn_mk]
    <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem esSpinProduct_eq_negOnePow_mul_spinProd_toIsing (A : Finset V)
    (sigma : V -> Fin 2) :
    esSpinProduct A sigma = (-1 : Real) ^ A.card *
      Ising.spinProd A (IsingFK.toIsing sigma) := by
  unfold esSpinProduct Ising.spinProd
  simp_rw [isingSpin_eq_neg_spin_toIsing]
  calc
    (∏ x ∈ A, -Ising.spin (IsingFK.toIsing sigma) x) =
        ∏ x ∈ A, (-1 : Real) * Ising.spin (IsingFK.toIsing sigma) x := by
          apply Finset.prod_congr rfl
          intro x hx
          ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

omit [Fintype V] [DecidableEq V] in
theorem esSpinProduct_eq_spinProd_toIsing_of_even (A : Finset V)
    (hA : Even A.card) (sigma : V -> Fin 2) :
    esSpinProduct A sigma = Ising.spinProd A (IsingFK.toIsing sigma) := by
  rw [esSpinProduct_eq_negOnePow_mul_spinProd_toIsing, hA.neg_one_pow, one_mul]

theorem esMultiPoint_eq_firstMarginal_sum (p : Real) (A : Finset V) :
    esMultiPoint G p A =
      ∑ sigma : V -> Fin 2,
        esFirstMarginal G 2 p sigma * esSpinProduct A sigma := by
  unfold esMultiPoint esFirstMarginal
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [← Finset.sum_mul]
  ring


theorem isingExpectation_spinProd_eq_allClustersEvenProb
    (beta : Real) (A : Finset V) (hA : Even A.card) :
    Ising.isingExpectation G beta 0 (Ising.spinProd A) =
      allClustersEvenProb G (1 - Real.exp (-2 * beta)) A := by
  let e : (V -> Fin 2) ≃ ConfigSpace V :=
    Equiv.ofBijective _ IsingFK.toIsing_bijective
  calc
    Ising.isingExpectation G beta 0 (Ising.spinProd A) =
        ∑ sigma : V -> Fin 2,
          Ising.isingProb G beta 0 (IsingFK.toIsing sigma) *
            Ising.spinProd A (IsingFK.toIsing sigma) := by
              unfold Ising.isingExpectation
              simpa [e, Equiv.ofBijective_apply] using
                (e.sum_comp (fun s =>
                  Ising.isingProb G beta 0 s * Ising.spinProd A s)).symm
    _ = ∑ sigma : V -> Fin 2,
          esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
            esSpinProduct A sigma := by
              apply Finset.sum_congr rfl
              intro sigma hsigma
              rw [IsingFK.isingProb_eq_pottsProb G beta (2 * beta) 1 (by ring),
                ← esFirstMarginal_eq_pottsProb G 2 (2 * beta) 1]
              simp only [mul_one]
              ring_nf
              rw [esSpinProduct_eq_spinProd_toIsing_of_even A hA]
    _ = esMultiPoint G (1 - Real.exp (-2 * beta)) A :=
      (esMultiPoint_eq_firstMarginal_sum G _ A).symm
    _ = allClustersEvenProb G (1 - Real.exp (-2 * beta)) A :=
      esMultiPoint_eq_allClustersEvenProb G _ A

end StatMech.FK
