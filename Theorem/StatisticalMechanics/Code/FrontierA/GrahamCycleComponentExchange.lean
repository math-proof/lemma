/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem exchangeCyclePair_leftInverse
    {K L A B : Finset I} (hKL : Disjoint K L)
    (hAK : A ⊆ K) (hBL : B ⊆ L)
    {P Q : Finset I} (hPK : P ⊆ K) (hQL : Q ⊆ L) :
    exchangeCyclePair B A (exchangeCyclePair A B (P, Q)) = (P, Q) := by
  apply Prod.ext <;> ext i
  · have hPB : i ∈ P → i ∈ B → False := fun hiP hiB =>
      Finset.disjoint_left.mp hKL (hPK hiP) (hBL hiB)
    have hQA : i ∈ Q → i ∈ A → False := fun hiQ hiA =>
      Finset.disjoint_left.mp hKL (hAK hiA) (hQL hiQ)
    simp only [exchangeCyclePair, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter, Prod.fst, Prod.snd]
    by_cases hiA : i ∈ A <;> aesop
  · have hPB : i ∈ P → i ∈ B → False := fun hiP hiB =>
      Finset.disjoint_left.mp hKL (hPK hiP) (hBL hiB)
    have hQA : i ∈ Q → i ∈ A → False := fun hiQ hiA =>
      Finset.disjoint_left.mp hKL (hAK hiA) (hQL hiQ)
    simp only [exchangeCyclePair, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter, Prod.fst, Prod.snd]
    by_cases hiB : i ∈ B <;> aesop

theorem sources_cycle_component_part
    {ends : I → Sym2 W} {P K : Finset I} (hPK : P ⊆ K)
    (hP : sources ends P = ∅) (u : W) :
    sources ends (P ∩ edgeComponent ends K u) = ∅ := by
  rw [sources_inter_edgeComponent hPK, hP]
  simp

theorem sources_cycle_component_complement
    {ends : I → Sym2 W} {P K : Finset I} (hPK : P ⊆ K)
    (hP : sources ends P = ∅) (u : W) :
    sources ends (P \ edgeComponent ends K u) = ∅ := by
  classical
  have hpart := sources_cycle_component_part hPK hP u
  have heq : P \ edgeComponent ends K u =
      P \ (P ∩ edgeComponent ends K u) := by
    ext i
    simp
  rw [heq, sources_sdiff_of_subset Finset.inter_subset_left, hP, hpart]
  simp


end StatMech.GrahamGHS.FourColor
