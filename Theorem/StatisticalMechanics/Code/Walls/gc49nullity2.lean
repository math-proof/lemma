/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc49_sd_oxyg_yg {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({y, g} : Finset W) = ({o, x} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inl rfl, not_or.2 ⟨hoy, hog⟩⟩
    · exact Or.inl ⟨Or.inr (Or.inl rfl), not_or.2 ⟨hxy, hxg⟩⟩


theorem gc49_complSubUniverse_sources (ends : ι → Sym2 W) {o x y g : W}
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    {n₁ : Finset ι} (hn₁ : sources ends n₁ = (∅ : Finset W)) :
    sources ends (univ \ n₁) = ({o, x, y, g} : Finset W) := by
  rw [gc40_sources_compl, huniv, hn₁]
  rw [show (∅ : Finset W) = (⊥ : Finset W) from rfl, symmDiff_bot]


theorem gc49_switching_ox_of_oxyg (ends : ι → Sym2 W) (V : Finset ι)
    (hnd : ∀ i ∈ V, ¬ (ends i).IsDiag) {o x y g : W}
    (hVsrc : sources ends V = ({o, x, y, g} : Finset W))
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    #(V.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))
      = (if connK ends V y g then
          #(V.powerset.filter (fun K => sources ends K = ({o, x, y, g} : Finset W))) else 0) := by
  have hsd : ({o, x, y, g} : Finset W) ∆ ({y, g} : Finset W) = ({o, x} : Finset W) :=
    gc49_sd_oxyg_yg hoy hog hxy hxg
  have hsw := switching_card ends V hnd ({o, x, y, g} : Finset W) hVsrc (u := y) (v := g) hyg
  rw [hsd] at hsw
  exact hsw


theorem gc49_LHSdoubled_card_eq_sum (ends : ι → Sym2 W) (o x y g : W) :
    #(gc48_LHSdoubled ends o x y g)
      = ∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)),
          #((univ \ n₁).powerset.filter
            (fun n₂ => sources ends n₂ = ({o, x} : Finset W) ∧ connK ends (n₁ ∪ n₂) x g)) := by
  rw [gc48_LHSdoubled]
  exact gc40_pairCount_reindex (P := fun S => sources ends S = (∅ : Finset W))
    (Q := fun n₁ n₂ => sources ends n₂ = ({o, x} : Finset W) ∧ connK ends (n₁ ∪ n₂) x g)


theorem gc49_RHSdoubled_card_eq_sum (ends : ι → Sym2 W) (o x y g : W) :
    #(gc48_RHSdoubled ends o x y g)
      = ∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)),
          #((univ \ n₁).powerset.filter
            (fun m₂ => sources ends m₂ = ({o, x, y, g} : Finset W)
              ∧ connK ends (n₁ ∪ m₂) o x ∧ connK ends (n₁ ∪ m₂) o y ∧ connK ends (n₁ ∪ m₂) o g)) := by
  rw [gc48_RHSdoubled]
  exact gc40_pairCount_reindex (P := fun S => sources ends S = (∅ : Finset W))
    (Q := fun n₁ m₂ => sources ends m₂ = ({o, x, y, g} : Finset W)
      ∧ connK ends (n₁ ∪ m₂) o x ∧ connK ends (n₁ ∪ m₂) o y ∧ connK ends (n₁ ∪ m₂) o g)


end Abstract
end StatMech.Walls
