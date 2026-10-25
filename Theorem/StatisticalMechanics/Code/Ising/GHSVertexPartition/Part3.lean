/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part2
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


theorem ghsvp_vertexCorr_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e, 0 <= J e) (S P : Finset W) :
    0 <= ghsvp_vertexCorr E J S P := by
  exact ghsvp_expJ_zero_nonneg _ J (fun e _ => hJ e) P


theorem ghsvp_vertexCorr_mono (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e, 0 <= J e) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {S T : Finset W} (hST : S ⊆ T) (P : Finset W) :
    ghsvp_vertexCorr E J S P <= ghsvp_vertexCorr E J T P := by
  unfold ghsvp_vertexCorr
  apply griffiths_mono (ghsvp_vertexEdges E S) (ghsvp_vertexEdges E T) J
    (fun _ => 0) ((ghsvp_vertexEdges_mono E) hST)
  · exact fun e _ => hJ e
  · exact fun _ => le_rfl
  · intro e he _
    exact hnd e (Finset.mem_filter.mp he).1

theorem ghsvp_vertexCorrField_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (S P : Finset W) : 0 <= ghsvp_vertexCorrField E J hf S P := by
  exact ghsvp_expJ_nonneg _ J hf (fun e _ => hJ e) hhf P

theorem ghsvp_vertexCorrField_mono (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (hnd : ∀ e ∈ E, ¬ e.IsDiag) {S T : Finset W} (hST : S ⊆ T) (P : Finset W) :
    ghsvp_vertexCorrField E J hf S P <= ghsvp_vertexCorrField E J hf T P := by
  unfold ghsvp_vertexCorrField
  apply griffiths_mono (ghsvp_vertexEdges E S) (ghsvp_vertexEdges E T) J hf
    ((ghsvp_vertexEdges_mono E) hST)
  · exact fun e _ => hJ e
  · exact hhf
  · intro e he _
    exact hnd e (Finset.mem_filter.mp he).1


end StatMech.Ising
