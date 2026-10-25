/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexVBC_vertexBound (a : ℂ) (h0 : ℤ) (W : HexWalk)
    (hmids : ∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
    ∀ x ∈ W.vertices, x ∈ hexVBC_adjClosure a h0 := by
  intro x hx
  obtain ⟨mm, hmm, hh, hxe⟩ :=
    hexVBC_vert_eq_mid_plus_step W.startMid W.h0 W.turns x (by rw [← HexWalk.vertices]; exact hx)
  have hmmem : mm ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) :=
    hmids mm (by rw [HexWalk.mids]; exact hmm)
  obtain ⟨α, β, hstep, hin⟩ := hexVBC_halfStep_classify h0 hh
  rw [hxe, hstep]
  unfold hexVBC_adjClosure
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmmem
  rcases hmmem with h | h | h <;> subst h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hexVBC_star_mem _ _ α β hin))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hexVBC_star_mem _ _ α β hin))
  · exact Finset.mem_union_right _ (hexVBC_star_mem _ _ α β hin)


end StatMech.Universality
