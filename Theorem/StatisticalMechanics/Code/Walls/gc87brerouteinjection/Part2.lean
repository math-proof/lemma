/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean -/

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
import Def.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part2
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


theorem gc87b_residual_of_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc86b_CogxgResidual ends m o x y g := by
  unfold gc86b_CogxgResidual
  unfold gc87b_CogxgLeT3 at hle
  have h2 : 2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g :=
    gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog
  have hcog : (gc85b_pcount ends m {o, g} {x, g} : ℤ) ≤ (gc87b_T3 ends m o x y g : ℤ) := by
    exact_mod_cast hle
  
  have : gc87b_slack ends m o x y g
      = ((gc85b_pcount ends m ∅ {o, g} : ℤ) + (gc85b_pcount ends m ∅ {o, x} : ℤ)
          + (gc85b_pcount ends m ∅ {o, y} : ℤ)) - (gc85b_pcount ends m ∅ ∅ : ℤ) := rfl
  linarith


theorem gc87b_bijection_of_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc86b_bijection_of_residual ends m o x y g
    (gc87b_residual_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle)


end StatMech.Walls
