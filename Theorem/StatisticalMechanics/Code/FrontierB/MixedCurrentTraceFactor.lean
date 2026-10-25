/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Def.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceFactor
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]

omit [Countable E] in
theorem pairOrConfig_preimage_cylinder [DecidableEq E]
    (S : Finset E) (A : Set (↑S -> Bool)) :
    pairOrConfig ⁻¹' MeasureTheory.cylinder S A =
      MeasureTheory.cylinder (pairOrSupport S) (pairOrPullbackPatternSet S A) := by
  ext omega
  change (fun e : ↑S => omega (Sum.inl e.1) || omega (Sum.inr e.1)) ∈ A ↔
    pairOrLocalPattern S (Finset.restrict (pairOrSupport S) omega) ∈ A
  have hpattern : (fun e : ↑S =>
      omega (Sum.inl e.1) || omega (Sum.inr e.1)) =
      pairOrLocalPattern S (Finset.restrict (pairOrSupport S) omega) := by
    funext e
    rfl
  rw [hpattern]


theorem pairOrConfig_preimage_mem_measurableCylinders
    {C : Set (ConfigSpace E)}
    (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
    pairOrConfig ⁻¹' C ∈ measurableCylinders (fun _ : E ⊕ E => Bool) := by
  classical
  rw [mem_measurableCylinders] at hC ⊢
  obtain ⟨S, A, hA, rfl⟩ := hC
  exact ⟨pairOrSupport S, pairOrPullbackPatternSet S A,
    MeasurableSet.of_discrete, pairOrConfig_preimage_cylinder S A⟩


end StatMech.FrontierB
