/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean -/

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
import Def.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part3
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


theorem gc86b_star_sources :
    sources gc86b_starEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  decide


theorem gc86b_star_bijection :
    gc85b_ThreeCurrentBijection gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3
      ∧ gc85b_pcount gc86b_starEnds (univ : Finset (Fin 4)) ∅ ∅ = 1 := by
  refine ⟨?_, ?_⟩
  · unfold gc85b_ThreeCurrentBijection gc85b_pcount; decide
  · unfold gc85b_pcount; decide


theorem gc86b_reroute_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (connK ends m o x ∨ connK ends m o y ∨ connK ends m o g)
    
    ∧ (gc85b_pcount ends m ∅ ∅
        ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y})
    
    ∧ (gc86b_CogxgResidual ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨gc86b_o_connects_mark ends m hnd hsrc hox hoy hog,
   gc86b_strong_global ends m hnd hsrc hox hoy hog,
   (gc86b_bijection_iff_residual ends m o x y g).symm⟩

end StatMech.Walls
