/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Def.StatisticalMechanics.Code.OSSS.ReachDomination
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace ReachDomination

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem reachOpen_stable_to_B {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x b : V} (hb : b ∈ B) (h : ReachOpen endU endV X x b) :
    ReachOpen endU endV w x b := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | @step a c z e hopen hpair hrest ih =>
      
      
      
      have hcB : ConnOpenSet endU endV X c B := ⟨z, hb, hrest⟩
      have hincid : IncidentCluster endU endV X B e := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · 
          exact Or.inr (by rw [hV]; exact hcB)
        · 
          exact Or.inl (by rw [hU]; exact hcB)
      have hwopen : w e = true := by rw [hagree e hincid]; exact hopen
      exact ReachOpen.step e hwopen hpair (ih hb)

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_stable_of_agree {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x : V} (h : ConnOpenSet endU endV X x B) :
    ConnOpenSet endU endV w x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_stable_to_B hagree hbB hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem reachOpen_stable_from_B {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {b y : V} (hb : ConnOpenSet endU endV X b B) (h : ReachOpen endU endV w b y) :
    ConnOpenSet endU endV X y B := by
  induction h with
  | refl x => exact hb
  | @step a c z e hopen hpair hrest ih =>
      
      
      
      have hincid : IncidentCluster endU endV X B e := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · exact Or.inl (by rw [hU]; exact hb)
        · exact Or.inr (by rw [hV]; exact hb)
      have hXopen : X e = true := by rw [← hagree e hincid]; exact hopen
      
      have hcB : ConnOpenSet endU endV X c B := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · 
          have hbU : ConnOpenSet endU endV X (endU e) B := by rw [hU]; exact hb
          have := connOpenSet_prop hXopen hbU
          rwa [hV] at this
        · 
          have hbV : ConnOpenSet endU endV X (endV e) B := by rw [hV]; exact hb
          have := connOpenSet_prop' hXopen hbV
          rwa [hU] at this
      exact ih hcB

omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem connOpenSet_iff_of_agree {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
    {x : V} :
    ConnOpenSet endU endV w x B ↔ ConnOpenSet endU endV X x B := by
  constructor
  · rintro ⟨b, hbB, hreach⟩
    exact reachOpen_stable_from_B hagree (connOpenSet_of_mem hbB) (reachOpen_symm hreach)
  · exact connOpenSet_stable_of_agree hagree


end ReachDomination
end OSSS
end StatMech
