/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc60exhaustive.Part2
import Def.StatisticalMechanics.Code.Walls.gc61parallelg
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
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc61_rerouteConnector_of_parallelTwin (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc61_ParallelTwinPresent ends K o x y g) :
    gc59_RerouteConnector ends K o x y g := by
  obtain ⟨D, i, v, hDV, hDsrc, hi, hvg, hL⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hLmem
  obtain ⟨hgate, hcase⟩ := hL L hLmem
  rcases hcase with ⟨hDinter, hiKL, hreconn⟩ | hDempty
  · 
    refine ⟨[i], ?_, ?_, hgate⟩
    · simp [hDinter]
    · refine ⟨hiKL, ⟨v, g, hi, hreconn⟩, ?_⟩
      simp [gc59_Peelable]
  · 
    refine ⟨[], ?_, trivial, hgate⟩
    simp [hDempty]


theorem gc61_disjointConnector_of_parallelTwin (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc61_ParallelTwinPresent ends K o x y g) :
    gc57_DisjointConnector ends K o x y g :=
  gc59_disjointConnector_of_reroute ends K (gc61_rerouteConnector_of_parallelTwin ends K h)


theorem gc61_disjointConnector_all (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov :
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc61_ParallelTwinPresent ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | hg1 | hyge | hdisj | htwin
  · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
  · exact gc61_disjointConnector_of_parallelTwin ends K htwin


theorem gc61_countIneq_of_cover (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc61_ParallelTwinPresent ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc61_disjointConnector_all ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)

end Abstract
end StatMech.Walls
