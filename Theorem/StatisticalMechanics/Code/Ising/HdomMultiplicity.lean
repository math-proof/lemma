/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Ising.HdomMultiplicity
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem hmu_addBackbone_apply (P : Finset (Sym2 V)) (m : Current V) (e : Sym2 V) :
    hmu_addBackbone P m e = m e + (if e ∈ P then 1 else 0) := rfl


theorem hmu_addBackbone_injective (P : Finset (Sym2 V)) :
    Function.Injective (hmu_addBackbone (V := V) P) := by
  intro m₁ m₂ h
  funext e
  have he := congrFun h e
  simp only [hmu_addBackbone_apply] at he
  omega


theorem hmu_addBackbone_even_on (m : Current V) (P : Finset (Sym2 V))
    (hPodd : ∀ e ∈ P, Odd (m e)) {e : Sym2 V} (he : e ∈ P) :
    Even (hmu_addBackbone P m e) := by
  simp only [hmu_addBackbone_apply, if_pos he]
  exact (hPodd e he).add_one


theorem hmu_addBackbone_oddEdges_disjoint (m : Current V) (P : Finset (Sym2 V))
    (hPodd : ∀ e ∈ P, Odd (m e)) :
    Disjoint (oddEdges G.edgeFinset (hmu_addBackbone P m)) P := by
  rw [Finset.disjoint_left]
  intro e he heP
  rw [oddEdges, Finset.mem_filter] at he
  exact (Nat.not_even_iff_odd.mpr he.2) (hmu_addBackbone_even_on m P hPodd heP)


theorem hmu_addBackbone_oddEdges_off (m : Current V) (P : Finset (Sym2 V))
    {e : Sym2 V} (he : e ∉ P) :
    Odd (hmu_addBackbone P m e) ↔ Odd (m e) := by
  simp only [hmu_addBackbone_apply, if_neg he, add_zero]


theorem hmu_addBackbone_posEdges_mono (m : Current V) (P : Finset (Sym2 V)) :
    posEdges G.edgeFinset m ⊆ posEdges G.edgeFinset (hmu_addBackbone P m) := by
  intro e he
  rw [posEdges, Finset.mem_filter] at he ⊢
  refine ⟨he.1, ?_⟩
  simp only [hmu_addBackbone_apply]
  have := he.2
  omega


theorem hmu_addBackbone_connPos_preserved (m : Current V) (P : Finset (Sym2 V))
    {u v : V} (h : connP (posEdges G.edgeFinset m) u v) :
    connP (posEdges G.edgeFinset (hmu_addBackbone P m)) u v :=
  connP_mono (hmu_addBackbone_posEdges_mono G m P) h


theorem hmu_addBackbone_weight_ratio (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (P : Finset (Sym2 V)) :
    Sharpness.weight G β J (hmu_addBackbone P m)
      = Sharpness.weight G β J m
        * ∏ e ∈ G.edgeFinset, (if e ∈ P then (β * J e) / (m e + 1) else 1) :=
  hnw_addBackbone_weight G β J m P


theorem hmu_weight_pos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 < β) (hJ : ∀ e, 0 < J e)
    (m : Current V) : 0 < Sharpness.weight G β J m := by
  unfold Sharpness.weight
  refine Finset.prod_pos (fun e _ => ?_)
  exact div_pos (pow_pos (mul_pos hβ (hJ e)) _) (by exact_mod_cast Nat.factorial_pos _)


theorem hmu_mass_ge_weight (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) :
    Sharpness.weight G β J m ≤ hnw_mass G β J m (Sharpness.sources G m) := by
  unfold hnw_mass splitWeightedSum
  set f : {K : Current V // ∀ e, K e ≤ m e} → ℝ :=
    fun K => (if Sharpness.sources G K.1 = Sharpness.sources G m
      then (1:ℝ) * (Sharpness.weight G β J K.1
        * Sharpness.weight G β J (fun e => m e - K.1 e))
      else 0) with hf
  have hnn : ∀ K ∈ Finset.univ, 0 ≤ f K := by
    intro K _; rw [hf]; dsimp only
    split
    · rw [one_mul]
      exact mul_nonneg (asd_weight_nonneg G β J hβ hJ _) (asd_weight_nonneg G β J hβ hJ _)
    · exact le_refl _
  have hterm : Sharpness.weight G β J m ≤ f ⟨m, fun e => le_refl _⟩ := by
    rw [hf]; dsimp only
    rw [if_pos rfl, one_mul]
    have hzero : (fun e => m e - m e) = (fun _ => 0) := by funext e; omega
    rw [hzero, Sharpness.weight_zero, mul_one]
  calc Sharpness.weight G β J m
      ≤ f ⟨m, fun e => le_refl _⟩ := hterm
    _ ≤ ∑ K : {K : Current V // ∀ e, K e ≤ m e}, f K :=
        Finset.single_le_sum hnn (Finset.mem_univ _)


theorem hmu_mass_pos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 < β) (hJ : ∀ e, 0 < J e)
    (m : Current V) : 0 < hnw_mass G β J m (Sharpness.sources G m) :=
  lt_of_lt_of_le (hmu_weight_pos G β J hβ hJ m)
    (hmu_mass_ge_weight G β J (le_of_lt hβ) (fun e => le_of_lt (hJ e)) m)


end Ising
end StatMech
