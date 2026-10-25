/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc52switchinj.Part2
import Def.StatisticalMechanics.Code.Walls.gc53count.Part2
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
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc53_LblockSet_eq_gateBlock (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) :
    gc51_LblockSet ends K o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := rfl


theorem gc53_Lblock_le_Rblock_of_cosetGateDom (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g)
    (K : Finset ι) (hK : K ∈ (univ : Finset ι).powerset.filter
      (fun K => sources ends K = ({o, x} : Finset W))) :
    #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  obtain ⟨P₀, hP₀sub, hP₀src⟩ :=
    gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  have h1 : #(gc51_LblockSet ends K o x g) ≤ #(gc53_cosetGateBlock ends K P₀ o x g) :=
    hdom K hK P₀ hP₀sub hP₀src
  have h2 : #(gc51_RblockSet ends K o x y g) = #(gc53_cosetGateBlock ends K P₀ o x g) :=
    gc53_Rblock_card_eq_cosetGate ends hnd K hox hyg hKsrc hP₀sub hP₀src
  rw [h2]; exact h1


theorem gc53_perKCount_of_cosetGateDom (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g) :
    gc52_PerKCount ends o x y g := by
  intro K hK
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  exact gc53_Lblock_le_Rblock_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom K hK


theorem gc53_countIneq_of_cosetGateDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc52_countIneq_of_perKCount ends hnd hox hoy hog hxy hxg hyg huniv
    (gc53_perKCount_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom)

end Abstract

open Classical


theorem gc53_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK P₀ hP₀sub hP₀src
  
  have hKsrc : sources gc49_witnessEnds K = ({0, 1} : Finset (Fin 4)) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  have hbij : #(gc51_RblockSet gc49_witnessEnds K 0 1 2 3)
      = #(gc53_cosetGateBlock gc49_witnessEnds K P₀ 0 1 3) :=
    gc53_Rblock_card_eq_cosetGate gc49_witnessEnds gc49_witnessEnds_loopless K
      (by decide) (by decide) hKsrc hP₀sub hP₀src
  rw [← hbij]
  
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · rw [gc51_witness_LblockSet_K13, gc51_witness_RblockSet_K13, Finset.card_singleton,
      Finset.card_singleton]
  · rw [gc51_witness_LblockSet_K23, gc51_witness_RblockSet_K23, Finset.card_singleton,
      Finset.card_singleton]


theorem gc53_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc53_witness_cosetGateDom


theorem gc53_witness_Rblock_gate_K13 :
    gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3
      = (univ \ ({1, 3} : Finset (Fin 4))).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 1 3) :=
  gc53_Rblock_eq_gateBlock gc49_witnessEnds gc49_witnessEnds_loopless
    ({1, 3} : Finset (Fin 4)) (by decide) (by decide) (by decide)

end StatMech.Walls
