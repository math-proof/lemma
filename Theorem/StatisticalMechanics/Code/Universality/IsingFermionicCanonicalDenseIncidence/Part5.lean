/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part5
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem fkIsing_floor_mul_succ_eventually_in_expandingSquare (c : Real) :
    ∀ᶠ k : Nat in atTop,
      -(fkIsingExpandingSquareSide k : Int) ≤ ⌊c * (k + 1 : Real)⌋ ∧
        ⌊c * (k + 1 : Real)⌋ < fkIsingExpandingSquareSide k := by
  obtain ⟨M : Nat, hM⟩ := exists_nat_ge |c|
  filter_upwards [eventually_ge_atTop (M + 1)] with k hk
  have ht : (M : Real) + 1 < (k + 1 : Real) := by
    exact_mod_cast (show M + 1 < k + 1 by omega)
  have htpos : 0 < (k + 1 : Real) := by positivity
  have hcUpper : c ≤ M := le_trans (le_abs_self c) hM
  have hcLower : -(M : Real) ≤ c := by
    exact le_trans (neg_le_neg hM) (neg_abs_le c)
  constructor
  · have hfloorLower :
        (-(fkIsingExpandingSquareSide k : Int) : Int) <
          ⌊c * (k + 1 : Real)⌋ := by
      have hside : (fkIsingExpandingSquareSide k : Real) =
          (k + 1 : Real) ^ 2 := by
        norm_num [fkIsingExpandingSquareSide]
      have hreal :
          -(fkIsingExpandingSquareSide k : Real) <
            ((⌊c * (k + 1 : Real)⌋ : Int) : Real) := by
        calc
          -(fkIsingExpandingSquareSide k : Real) <
              c * (k + 1 : Real) - 1 := by
                rw [hside]
                nlinarith
          _ < ((⌊c * (k + 1 : Real)⌋ : Int) : Real) :=
            Int.sub_one_lt_floor _
      exact_mod_cast hreal
    omega
  · rw [Int.floor_lt]
    have hside : (fkIsingExpandingSquareSide k : Real) =
        (k + 1 : Real) ^ 2 := by
      norm_num [fkIsingExpandingSquareSide]
    norm_cast
    rw [hside]
    push_cast
    nlinarith


theorem fkIsingDenseRationalPrimal_eventually_interior (q : Rat × Rat) :
    ∀ᶠ k : Nat in atTop,
      -(fkIsingExpandingSquareSide k : Int) ≤
          fkIsingDenseRationalPrimalX q k ∧
        fkIsingDenseRationalPrimalX q k < fkIsingExpandingSquareSide k ∧
      -(fkIsingExpandingSquareSide k : Int) ≤
          fkIsingDenseRationalPrimalY q k ∧
        fkIsingDenseRationalPrimalY q k < fkIsingExpandingSquareSide k := by
  filter_upwards
    [fkIsing_floor_mul_succ_eventually_in_expandingSquare
      (((q.1 : Real) + (q.2 : Real)) / 2),
     fkIsing_floor_mul_succ_eventually_in_expandingSquare
      (((q.1 : Real) - (q.2 : Real)) / 2)] with k hx hy
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩


end
end StatMech.Universality
