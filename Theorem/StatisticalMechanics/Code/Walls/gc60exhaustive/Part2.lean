/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc60exhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc59residual.Part4
import Def.StatisticalMechanics.Code.Walls.gc60exhaustive
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

open Classical


theorem gc60_witnessEnds_univ_sources :
    sources gc60_witnessEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc60_witnessEnds_K_sources :
    sources gc60_witnessEnds ({0} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc60_witnessEnds_loopless : ∀ i : Fin 3, ¬ (gc60_witnessEnds i).IsDiag := by decide


theorem gc60_witnessEnds_gDegOne :
    degK gc60_witnessEnds (univ : Finset (Fin 3)) (3 : Fin 4) = 1 := by decide


theorem gc60_witness_not_gateInK :
    ¬ connK gc60_witnessEnds ({0} : Finset (Fin 3)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 4, connK gc60_witnessEnds ({0} : Finset (Fin 3)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc60_witness_lblock_empty :
    gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3))) :=
  gc60_lblockSet_empty_of_gDegOne gc60_witnessEnds ({0} : Finset (Fin 3)) (y := 2)
    (by decide) (by decide) gc60_witnessEnds_K_sources gc60_witnessEnds_gDegOne


theorem gc60_witness_disjointConnector :
    gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 :=
  gc60_disjointConnector_of_gDegOne gc60_witnessEnds gc60_witnessEnds_loopless ({0} : Finset (Fin 3))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    gc60_witnessEnds_univ_sources gc60_witnessEnds_K_sources gc60_witnessEnds_gDegOne


theorem gc60_witness_no_ygEdge :
    ¬ ∃ i, i ∈ (univ : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) ∧ gc60_witnessEnds i = s(2, 3) := by
  decide


theorem gc60_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) →
        degK ends (univ : Finset ι) g = 1 →
          gc57_DisjointConnector ends K o x y g)
    ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (o x y g : W),
        o ≠ g → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
          degK ends (univ : Finset ι) g = 1 ∨ 3 ≤ degK ends (univ : Finset ι) g)
    ∧ gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3)))
    ∧ gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hoy hog hxy hxg hyg huniv hKsrc hg1 =>
      gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1,
    fun ends o x y g hog hxg hyg huniv => gc60_gDeg_dichotomy ends hog hxg hyg huniv,
    gc60_witness_lblock_empty,
    gc60_witness_disjointConnector⟩

end StatMech.Walls
