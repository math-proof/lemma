/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Def.StatisticalMechanics.Code.FK.BoxFeketePerVolume
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


theorem bpv_boxTiltFreeEnergy_tendsto (t : ℝ) (hdata : bpv_PerVolumeFreeEnergyData d t) :
    ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
  obtain ⟨δ, osc, hδ, hsum, hdymono, hbdd, hosc, hsand⟩ := hdata
  exact bpv_perVolume_converges (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) δ osc
    hδ hsum hdymono hbdd hosc hsand


theorem bpv_exists_convex_ivPressure_of_perVolume
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g := by
  classical
  have hconv : ∀ t, ∃ L : ℝ,
      Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) :=
    fun t => bpv_boxTiltFreeEnergy_tendsto t (hdata t)
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_⟩
  exact ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2)
    (fun t => (hconv t).choose)
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    (fun t => (hconv t).choose_spec)


theorem bpv_perVolumeFreeEnergyData_satisfiable :
    ∃ (g δ osc : ℕ → ℝ),
      (∀ j, 0 ≤ δ j)
      ∧ Summable δ
      ∧ (∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1)))
      ∧ BddAbove (range (fun j => g (2 ^ j)))
      ∧ Tendsto osc atTop (𝓝 0)
      ∧ (∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => le_refl 0, summable_zero, ?_, ?_,
    tendsto_const_nhds, ?_⟩
  · intro j; simp
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · intro n _; simp


theorem bpv_fk_uniqueness_of_perVolume (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
    (hcolfree : ubd_FreeGrowingBoxCollapse (d := d) N)
    (hcolwired : wpd_AvgWiredDensityCollapse (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hboxfree, hg⟩ := bpv_exists_convex_ivPressure_of_perVolume hEbox hdata
  exact ubd_fk_uniqueness_of_growingBoxCollapse hd N eb hEbox hg hboxfree hcolfree hcolwired


theorem bpv_fk_uniqueness_of_perVolume_rotation (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
    (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hboxfree, hg⟩ := bpv_exists_convex_ivPressure_of_perVolume hEbox hdata
  exact ocs_fk_uniqueness_of_rotation hd N eb hEbox hg hboxfree hfreeRot hwiredRot


theorem bpv_residue_remark : True := trivial

end FK
end StatMech
