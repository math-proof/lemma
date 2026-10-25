/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


@[simp] theorem hexSmallCellIncidence_mem (a : ℂ) (h0 : ℤ) (j : Fin 3) :
    hexSmallCellIncidence j ∈ (hexUncondDomain a h0).incidences := by
  simp [hexSmallCellIncidence, HexDomain.incidences, hexUncondDomain]

@[simp] theorem hexSmallCellIncidence_boundary_mem
    (a : ℂ) (h0 : ℤ) (j : Fin 3) :
    hexSmallCellIncidence j ∈
      (hexUncondDomain a h0).incidences \ (hexUncondPairing a h0).interior := by
  simp [hexUncondPairing]


theorem hexSmallCellIncidence_eq (a : ℂ) (h0 : ℤ)
    (e : HexIncidence (Fin 1)) (he : e ∈ (hexUncondDomain a h0).incidences) :
    e = hexSmallCellIncidence e.edge := by
  rcases e with ⟨v, j⟩
  fin_cases v
  rfl


theorem hexUncondMid_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexUncondMid a h0) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [hexUncondMid, hexConcrete_p_eq] at hij ⊢
  · exact (hexConcrete_a_ne_q a h0 hij).elim
  · exact (hexConcrete_a_ne_r a h0 hij).elim
  · exact (hexConcrete_a_ne_q a h0 hij.symm).elim
  · exact (hexConcrete_q_ne_r a h0 hij).elim
  · exact (hexConcrete_a_ne_r a h0 hij.symm).elim
  · exact (hexConcrete_q_ne_r a h0 hij.symm).elim


end StatMech.Universality
