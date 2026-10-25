/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketeData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Def.StatisticalMechanics.Code.FK.BoxFeketeData
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


variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]


variable {d : ℕ}


theorem bfd_boxTiltFreeEnergy_tendsto (t : ℝ)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hint : bfd_FKInterfaceData d t) :
    ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
  obtain ⟨c, κ, hsub, hbdd, hc, hκ, he⟩ := hint
  exact ⟨_, bfd_tiltFreeEnergy_tendsto_of_nearSubadditive (boxGraph d ·) 2 (by norm_num) t hE
    c hsub hbdd hc κ hκ he⟩


theorem bfd_exists_convex_ivPressure_of_interface
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hint : ∀ t, bfd_FKInterfaceData d t) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g := by
  classical
  
  have hconv : ∀ t, ∃ L : ℝ,
      Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) :=
    fun t => bfd_boxTiltFreeEnergy_tendsto t hE (hint t)
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_⟩
  
  exact ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2)
    (fun t => (hconv t).choose)
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    (fun t => (hconv t).choose_spec)


theorem bfd_fkInterfaceData_satisfiable :
    ∃ (u c : ℕ → ℝ) (e : ℕ → ℝ) (κ : ℝ),
      Subadditive (fun n => u n + c n)
      ∧ BddBelow (Set.range fun n => (u n + c n) / n)
      ∧ Tendsto (fun n => c n / n) atTop (𝓝 0)
      ∧ κ ≠ 0
      ∧ Tendsto (fun n => e n / n) atTop (𝓝 κ) := by
  refine ⟨fun _ => 0, fun _ => 0, fun n => (n : ℝ), 1, ?_, ?_, ?_, one_ne_zero, ?_⟩
  · intro m n; simp
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · simp only [zero_div]; exact tendsto_const_nhds
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp


theorem bfd_fk_uniqueness_of_interface_and_uniformBulk (hd : 1 ≤ d) (N : ℕ)
    (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hint : ∀ t, bfd_FKInterfaceData d t)
    (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
    (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hboxfree, hg⟩ := bfd_exists_convex_ivPressure_of_interface hEbox hint
  exact ubd_fk_uniqueness_of_uniformBulk hd N eb hEbox hg hboxfree hfreeBulk hwiredBulk


theorem bfd_residue_remark : True := trivial

end FK
end StatMech
