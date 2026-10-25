/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


variable (d : ℕ)


theorem agl_exists_convex_ivPressure (hd : 1 ≤ d)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g := by
  classical
  have hconv : ∀ t, ∃ L : ℝ,
      Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
    intro t
    obtain ⟨hdbl, hbdd, bj, osc, hbj, hosc, hsand⟩ := hdata t
    exact agl_boxTiltFreeEnergy_tendsto d t (fun j => hE (agl_K j)) hdbl hbdd bj hbj osc hosc hsand
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_⟩
  exact ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2)
    (fun t => (hconv t).choose)
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    (fun t => (hconv t).choose_spec)


theorem agl_fk_uniqueness_of_additiveData (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hboxfree, hg⟩ := agl_exists_convex_ivPressure d hd hEbox hdata
  exact fpe2_fk_uniqueness_of_boxFekete hd N eb heb hEbox hg hboxfree
    (gec_GenuineFreeCollapse hd N hEbox)
    (gec_GenuineWiredCollapse hd N hEbox)


theorem agl_additiveDoublingBound_satisfiable (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (u E : ℕ → ℝ),
      (∃ (I : ℕ → ℝ),
        (∀ j, 0 ≤ I j)
        ∧ Summable (fun j => I j / E (agl_K (j + 1)))
        ∧ (∀ j, u (agl_K (j + 1)) ≤ (2 : ℝ) ^ d * u (agl_K j) + I j * c)
        ∧ (∀ j, |(2 : ℝ) ^ d * E (agl_K j) - E (agl_K (j + 1))| ≤ I j)) := by
  refine ⟨fun _ => 0, fun n => (n:ℝ) ^ d,
    fun j => |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|, ?_, ?_, ?_, ?_⟩
  · intro j; exact abs_nonneg _
  · 
    have hgsum : Summable (fun j => (d : ℝ) * (1/2)^j) :=
      (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le
      (g := fun j => |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|
        / ((agl_K (j + 1) : ℝ)) ^ d)
      (fun j => by positivity)
      (f := fun j => (d : ℝ) * (1/2)^j) ?_ hgsum
    · intro j
      have hKpos : (0:ℝ) < (agl_K j : ℝ) := by exact_mod_cast (agl_K_pos j)
      have hKsucc : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
      
      have h2d : (2:ℝ)^d * (agl_K j : ℝ)^d = (2 * (agl_K j : ℝ))^d := by rw [mul_pow]
      have hKsuccR : ((agl_K (j + 1) : ℝ)) = 2 * (agl_K j : ℝ) + 1 := by
        rw [hKsucc]; push_cast; ring
      have hle : ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d
          ≤ d * ((agl_K (j + 1) : ℝ))^(d-1) := by
        have hpow := boxSV_pow_sub_pow_le (2 * (agl_K j : ℝ) + 1) (2 * (agl_K j : ℝ))
          (by positivity) (by linarith) d
        rw [show (2 * (agl_K j : ℝ) + 1) - 2 * (agl_K j : ℝ) = 1 by ring, one_mul] at hpow
        rw [hKsuccR]; linarith [hpow]
      have hEsuccpos : (0:ℝ) < ((agl_K (j + 1) : ℝ))^d := by
        have : (0:ℝ) < (agl_K (j + 1) : ℝ) := by exact_mod_cast (agl_K_pos (j+1))
        positivity
      rw [div_le_iff₀ hEsuccpos]
      
      have habs : |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|
          = ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d := by
        rw [h2d, abs_sub_comm, abs_of_nonneg]
        have : (2 * (agl_K j : ℝ))^d ≤ ((agl_K (j + 1) : ℝ))^d := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hKsuccR]; linarith
        linarith
      rw [habs]
      
      have hKge : (2:ℝ)^j ≤ (agl_K (j + 1) : ℝ) := by
        have hnat : (2:ℕ)^j ≤ agl_K (j+1) := by
          unfold agl_K
          have hstep : 2^j + 1 ≤ 2^(j+1+1) := by
            calc 2^j + 1 ≤ 2^j + 2^j := by have := Nat.one_le_two_pow (n := j); omega
              _ = 2^(j+1) := by ring
              _ ≤ 2^(j+1+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact_mod_cast hnat
      have hdfac : (d:ℝ) * ((agl_K (j + 1) : ℝ))^(d-1)
          ≤ (d:ℝ) * (1/2)^j * ((agl_K (j + 1) : ℝ))^d := by
        rw [show ((agl_K (j + 1) : ℝ))^d = ((agl_K (j + 1) : ℝ))^(d-1) * (agl_K (j + 1) : ℝ) by
          rw [← pow_succ]; congr 1; omega]
        have hpow1 : (0:ℝ) ≤ ((agl_K (j + 1) : ℝ))^(d-1) := by positivity
        have hhalf : (1:ℝ) ≤ (1/2)^j * (agl_K (j + 1) : ℝ) := by
          have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
          have hhalfpow : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div, inv_pow]
          rw [hhalfpow]
          calc (1:ℝ) = (2:ℝ)^j * ((2:ℝ)^j)⁻¹ := (mul_inv_cancel₀ h2jpos.ne').symm
            _ ≤ (agl_K (j + 1) : ℝ) * ((2:ℝ)^j)⁻¹ := by
                apply mul_le_mul_of_nonneg_right hKge (by positivity)
            _ = ((2:ℝ)^j)⁻¹ * (agl_K (j + 1) : ℝ) := by ring
        have hdK : (0:ℝ) ≤ (d:ℝ) * ((agl_K (j + 1) : ℝ))^(d-1) :=
          mul_nonneg (Nat.cast_nonneg _) hpow1
        nlinarith [hdK, hhalf, mul_nonneg hdK (by linarith [hhalf] : (0:ℝ) ≤ (1/2)^j * (agl_K (j + 1) : ℝ) - 1)]
      calc ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d
          ≤ d * ((agl_K (j + 1) : ℝ))^(d-1) := hle
        _ ≤ (d:ℝ) * (1/2)^j * ((agl_K (j + 1) : ℝ))^d := hdfac
  · intro j
    have : (0:ℝ) ≤ |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d| * c :=
      mul_nonneg (abs_nonneg _) hc
    simpa using this
  · intro j; exact le_refl _


theorem agl_residue_remark : True := trivial

end FK
end StatMech
