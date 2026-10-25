/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Instance.StatisticalMechanics.Code.Walls.rc76halladaptive.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 100000 in


theorem rc76_swapSet_reachable_iff_colType
    (p q : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    (∃ S ∈ (Finset.univ : Finset (Fin 2)).powerset, swapSet S p = q) ↔
      rc78_colTypeF q = rc78_colTypeF p := by
  decide +revert +kernel


theorem rc76_reachNbhdF_eq_rc78_nbhd
    (A B : Finset (ConfigSpace (Fin 2)))
    (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc76_reachNbhdF A B p = rc78_nbhd A B p := by
  ext q
  simp only [rc76_reachNbhdF, rc78_nbhd, rc75_prodF, Finset.mem_filter,
    Finset.mem_product, rc76_swapSet_reachable_iff_colType]


theorem rc76_marriage_iff_wall :
    ∀ A B : Finset (ConfigSpace (Fin 2)), rc76_marriage A B ↔ rc76_wall A B := by
  intro A B
  have hdom : rc78_PerOrbitDom A B := rc78_perOrbitDom_fin2 A B
  have hmar78 : rc78_Marriage A B := rc78_marriage_of_perOrbitDom A B hdom
  have hmar76 : rc76_marriage A B := by
    intro T hT
    simpa only [rc76_source, rc78_Marriage, rc76_reachNbhdF_eq_rc78_nbhd] using
      hmar78 T hT
  have hwall : rc76_wall A B := by
    have hplan := rc78_existsInjective_of_perOrbitDom A B hdom
    exact rc78_count_of_existsInjective A B hplan
  exact iff_of_true hmar76 hwall

set_option maxRecDepth 8000 in


theorem rc76_marriage_binds_at_proper_subset :
    ∃ T ∈ (rc76_source rc75_gA rc75_gB).powerset,
      T.Nonempty ∧ T ≠ rc76_source rc75_gA rc75_gB ∧
      (T.biUnion (fun p => rc76_reachNbhdF rc75_gA rc75_gB p)).card < (rc76_source rc75_gA rc75_gB).card := by
  decide

set_option maxRecDepth 8000 in


theorem rc76_count_insufficient_arbitrary_source :
    let S₀ : Finset (ConfigSpace (Fin 2)) := {rc75_cfg false true}
    let A : Finset (ConfigSpace (Fin 2)) := {rc75_cfg true false, rc75_cfg true true}
    let B : Finset (ConfigSpace (Fin 2)) := Finset.univ
    let src : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) := S₀ ×ˢ Finset.univ
    2 ^ 2 * S₀.card ≤ A.card * B.card ∧
      (src.biUnion (fun p => rc76_reachNbhdF A B p)).card < src.card := by
  decide

end StatMech.Walls
