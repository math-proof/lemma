/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice.Part2


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma tri_phi_posStep (c : Fin 3) : 1 ≤ triPhi (triStepVec (triPosStep c)) := by
  fin_cases c <;> decide


lemma triPhi_add (p q : TriSite) : triPhi (p + q) = triPhi p + triPhi q := by
  unfold triPhi; simp [Pi.add_apply]; ring


lemma triPhi_zero : triPhi (0 : TriSite) = 0 := by simp [triPhi]


end StatMech.Universality
