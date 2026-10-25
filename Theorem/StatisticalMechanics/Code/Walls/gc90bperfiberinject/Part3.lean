/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc90bperfiberinject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc89bmetricinjection.Part2
import Def.StatisticalMechanics.Code.Walls.gc90bperfiberinject.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc90b_star_sources :
    sources gc90b_starEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide


theorem gc90b_star_cogxgFibers :
    sources gc90b_starEnds ({2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
    ∧ sources gc90b_starEnds ({3} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
    ∧ sources gc90b_starEnds ({4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


theorem gc90b_star_canonical_merge :
    (({2} : Finset (Fin 5)) \ ({2} : Finset (Fin 5)) = (∅ : Finset (Fin 5)))
      ∧ (({3} : Finset (Fin 5)) \ ({3} : Finset (Fin 5)) = (∅ : Finset (Fin 5)))
      ∧ (({4} : Finset (Fin 5)) \ ({4} : Finset (Fin 5)) = (∅ : Finset (Fin 5))) := by
  refine ⟨by decide, by decide, by decide⟩


theorem gc90b_star_perJ1_fails :
    
    gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({2} : Finset (Fin 5))) ∅ = 2
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({3} : Finset (Fin 5))) ∅ = 2
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({4} : Finset (Fin 5))) ∅ = 2
    
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ = 4
    
      ∧ (2 + 2 + 2 : ℕ) > gc86b_ncount gc90b_starEnds
          ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide


theorem gc90b_perfiber_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g) :
    
    (∀ (K₁ P : Finset ι), P ⊆ K₁ →
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅)
    
    ∧ (∀ (φ : Finset ι → Finset ι),
        (∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g) →
        (∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
          ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
            gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) →
        gc85b_ThreeCurrentBijection ends m o x y g) := by
  refine ⟨fun K₁ P hP => gc90b_perK1_le ends hP, ?_⟩
  intro φ hφmem hcap
  exact gc90b_close_of_assignment ends m hnd hsrc hox hoy hog hxg φ hφmem hcap


theorem gc90b_machine_findings : True := trivial

end StatMech.Walls
