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
import Def.StatisticalMechanics.Code.Walls.gc90bperfiberinject
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


theorem gc90b_cogxg_eq_sum (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    gc85b_pcount ends m {o, g} {x, g}
      = ∑ K₁ ∈ gc90b_cogxgFibers ends m o x g, gc86b_ncount ends (m \ K₁) ∅ :=
  gc87b_cogxg_fiber_conn (o := o) (x := x) (y := y) (g := g) ends m hnd hxg


theorem gc90b_T3_eq_sum (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc87b_T3 ends m o x y g
      = ∑ J₁ ∈ gc90b_T3Fibers ends m o x y g, gc86b_ncount ends (m \ J₁) ∅ := rfl


theorem gc90b_cogxg_le_of_assignment (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g)
    (φ : Finset ι → Finset ι)
    (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
    (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
      ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
    gc85b_pcount ends m {o, g} {x, g} ≤ gc87b_T3 ends m o x y g := by
  rw [gc90b_cogxg_eq_sum ends m hnd hxg (o := o) (y := y), gc90b_T3_eq_sum ends m o x y g]
  
  have hfib :
      ∑ K₁ ∈ gc90b_cogxgFibers ends m o x g, gc86b_ncount ends (m \ K₁) ∅
        = ∑ J₁ ∈ gc90b_T3Fibers ends m o x y g,
            ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
              gc86b_ncount ends (m \ K₁) ∅ := by
    rw [Finset.sum_fiberwise_of_maps_to (g := φ)
          (fun K₁ hK₁ => hφmem K₁ hK₁)]
  rw [hfib]
  exact Finset.sum_le_sum hcap


theorem gc90b_close_of_assignment (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g)
    (φ : Finset ι → Finset ι)
    (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
    (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
      ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog
    (gc90b_cogxg_le_of_assignment ends m hnd hxg φ hφmem hcap)


end StatMech.Walls
