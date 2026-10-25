/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewrite
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingCovariance
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem drd_deltaRewrite_perEdge_dichotomy
    (ends : ι → Sym2 V)
    (covTerm : ℝ)
    (pairSum : (Finset ι → Prop) → ℝ)
    (hpairSum_add : ∀ (P₁ P₂ : Finset ι → Prop) [DecidablePred P₁] [DecidablePred P₂]
        [DecidablePred (fun m => P₁ m ∨ P₂ m)],
        (∀ m, ¬ (P₁ m ∧ P₂ m)) →
        pairSum (fun m => P₁ m ∨ P₂ m) = pairSum P₁ + pairSum P₂)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hloop : ∀ m : Finset ι, ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g})
    (hcov : covTerm = pairSum (fun m => ¬ connK ends m o g)) :
    covTerm
      = pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g))
        + pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
  classical
  refine sdr_deltaRewrite_perEdge covTerm pairSum hpairSum_add
    (disconn := fun m => ¬ connK ends m o g)
    (caseA := fun m => connK ends m o x ∧ connK ends m y g)
    (caseB := fun m => connK ends m o y ∧ connK ends m x g)
    hcov ?_
  
  intro m hdisc
  exact disconnect_dichotomy_prop ends m (hloop m) hox hoy hog hxy hxg hyg
    (hsrcSet m hdisc) hdisc


end Sharpness
end StatMech
