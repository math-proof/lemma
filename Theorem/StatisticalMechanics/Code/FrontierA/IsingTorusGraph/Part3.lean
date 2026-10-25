/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

theorem isingTorusIndexedEdge_mem_edgeFinset
    (p : IsingDyadicTorus d k × Fin d) :
    isingTorusIndexedEdge p ∈ (isingTorusGraph d k).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  exact ⟨p.2, Or.inl rfl⟩

theorem isingTorusStep_injective :
    Function.Injective
      (isingTorusStep : Fin d → IsingDyadicTorus d k) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [isingTorusStep, hij, isingTorus_zmod_one_ne_zero] at hi

theorem isingTorus_steps_add_ne_zero (i j : Fin d) :
    (isingTorusStep i : IsingDyadicTorus d k) + isingTorusStep j ≠ 0 := by
  intro h
  by_cases hij : i = j
  · subst j
    have hi := congrFun h i
    have hi' : (2 : ZMod (2 ^ (k + 2))) = 0 := by
      simpa only [Pi.add_apply, isingTorusStep, Pi.single_eq_same,
        Pi.zero_apply, one_add_one_eq_two] using hi
    exact isingTorus_zmod_two_ne_zero hi'
  · have hi := congrFun h i
    simp [isingTorusStep, hij, isingTorus_zmod_one_ne_zero] at hi

theorem isingTorusIndexedEdge_injective :
    Function.Injective
      (isingTorusIndexedEdge :
        IsingDyadicTorus d k × Fin d → Sym2 (IsingDyadicTorus d k)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  unfold isingTorusIndexedEdge at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hxy, hstep⟩ | ⟨hcross, hcross'⟩
  · change x = y at hxy
    change x + isingTorusStep i = y + isingTorusStep j at hstep
    subst y
    have hij : i = j := isingTorusStep_injective
      (add_left_cancel hstep)
    subst j
    rfl
  · change x = y + isingTorusStep j at hcross
    change x + isingTorusStep i = y at hcross'
    subst x
    have hzero :
        (isingTorusStep j : IsingDyadicTorus d k) +
          isingTorusStep i = 0 := by
      apply add_left_cancel (a := y)
      simpa [add_assoc] using hcross'
    exact (isingTorus_steps_add_ne_zero j i hzero).elim

theorem isingTorusIndexedEdge_surjective :
    Function.Surjective
      (fun p : IsingDyadicTorus d k × Fin d =>
        (⟨isingTorusIndexedEdge p,
          isingTorusIndexedEdge_mem_edgeFinset p⟩ :
          (isingTorusGraph d k).edgeFinset)) := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        isingTorusGraph_adj_iff] at he
      rcases he with ⟨i, h | h⟩
      · refine ⟨(x, i), ?_⟩
        apply Subtype.ext
        simp [isingTorusIndexedEdge, h]
      · refine ⟨(y, i), ?_⟩
        apply Subtype.ext
        simp [isingTorusIndexedEdge, h, Sym2.eq_swap]


end StatMech.FrontierA
