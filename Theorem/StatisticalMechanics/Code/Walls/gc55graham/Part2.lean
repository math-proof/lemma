/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc55graham.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc54cosetgate.Part2
import Def.StatisticalMechanics.Code.Walls.gc55graham
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc55_removalSurvival_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc55_RemovalSurvival ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  rwa [Finset.sdiff_eq_self_of_disjoint (hdisj L hLmem)]


theorem gc55_removalSurvival_of_ygEdge (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    gc55_RemovalSurvival ends K o x y g := by
  refine ⟨{i}, ?_, ?_, ?_⟩
  · simpa using hiV
  · exact gc55_sources_singleton ends i hyg hi
  · intro L hL
    exact gc55_singleEdge_removal_survival ends hnd K hyg hiV hi hL


theorem gc55_gateShiftInjection_of_removalSurvival (ends : ι → Sym2 W) (K P₀ : Finset ι) {o x y g : W}
    (hP₀V : P₀ ⊆ univ \ K) (hP₀src : sources ends P₀ = ({y, g} : Finset W))
    (h : gc55_RemovalSurvival ends K o x y g) :
    gc54_GateShiftInjection ends K P₀ o x g := by
  obtain ⟨D, hDV, hDsrc, hsurv⟩ := h
  refine ⟨D ∆ P₀, ?_, ?_, ?_⟩
  · 
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hDV h
    · exact hP₀V h
  · 
    rw [sources_symmDiff, hDsrc, hP₀src, symmDiff_self]; rfl
  · 
    intro L hL
    have hkey : (L ∆ (D ∆ P₀)) ∆ P₀ = L ∆ D := by
      rw [symmDiff_assoc, symmDiff_symmDiff_cancel_right]
    rw [hkey]
    exact gc55_gate_removal_to_symmDiff ends K (hsurv L hL)


theorem gc55_cosetGateDom_of_removalSurvival (ends : ι → Sym2 W) {o x y g : W}
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc55_RemovalSurvival ends K o x y g) :
    gc53_CosetGateDom ends o x y g := by
  apply gc54_cosetGateDom_of_gateShiftInjection
  intro K hK P₀ hP₀sub hP₀src
  exact gc55_gateShiftInjection_of_removalSurvival ends K P₀ hP₀sub hP₀src (h K hK)


theorem gc55_countIneq_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc55_RemovalSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc53_countIneq_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv
    (gc55_cosetGateDom_of_removalSurvival ends h)

end Abstract

open Classical


theorem gc55_witness_removalSurvival_K13 :
    gc55_RemovalSurvival gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc55_removalSurvival_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc55_witness_removalSurvival_K23 :
    gc55_RemovalSurvival gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc55_removalSurvival_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc55_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc55_witness_removalSurvival_K13
  · exact gc55_witness_removalSurvival_K23


theorem gc55_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc55_witness_cosetGateDom


theorem gc55_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x y g : W),
      P₀ ⊆ univ \ K → sources ends P₀ = ({y, g} : Finset W) →
        gc55_RemovalSurvival ends K o x y g → gc54_GateShiftInjection ends K P₀ o x g)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K P₀ o x y g hP hPs h =>
      gc55_gateShiftInjection_of_removalSurvival ends K P₀ hP hPs h,
    gc55_witness_cosetGateDom, gc55_witness_perKCount⟩

end StatMech.Walls
