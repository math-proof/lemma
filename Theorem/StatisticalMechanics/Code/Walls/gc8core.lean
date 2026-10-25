/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc6_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
import Theorem.StatisticalMechanics.Code.Walls.gc8innereq15
import Theorem.StatisticalMechanics.Code.Walls.gc8reinnerpair
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Theorem.StatisticalMechanics.Code.Walls.gc8munonneg
import Theorem.StatisticalMechanics.Code.Walls.gc8fourmarks
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc8_core_claim1_lower_bound (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) (eΛ : ℝ)
    (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
    eΛ * Sharpness.currentSum S β J ({y, g} : Finset V)
      ≥ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ :=
  gc8_inner_eq15_claim1_step S β J hβ hJ y g eΛ hgriff


theorem gc8_core_claim1_eqclaim_lower_bound (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) (eΛ : ℝ)
    (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
    eΛ * Sharpness.currentSum S β J ({y, g} : Finset V)
      ≥ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ := by
  have hstep := gc8_core_claim1_lower_bound S β J hβ hJ y g eΛ hgriff
  have hrepair := gc8r_reinner_pair_unconditional S β J ({y, g} : Finset V)
  rw [ge_iff_le, ← hrepair]
  exact hstep


theorem gc8_core_claim1_eqclaim_lower_bound_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (y g : V) :
    0 ≤ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ :=
  div_nonneg (sq_nonneg _) (gc8_inner_eq15_sourceless_pos S β J).le


theorem gc8_core_claim1_lower_bound_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) :
    0 ≤ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ :=
  mul_nonneg (sq_nonneg _) (Ising.acr_currentSum_nonneg S β J hβ hJ ∅)


theorem gc8_core_claim1_normaliser_nonneg (GΛ GS : SimpleGraph V) [DecidableRel GΛ.Adj]
    [DecidableRel GS.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y g : V)
    (Jghost : Sym2 (Option V) → ℝ) :
    0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))
        * (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2
        * isingExpectation GS β h (spinProd ({o, x} : Finset V))
        * (Sharpness.currentSum (withGhost GΛ) β Jghost ∅) ^ 2 := by
  have hμ := gc8_mu_nonneg GΛ β h hβ hh o x y g
  have hox := gc8_twoPoint_nonneg GS β h hβ hh o x
  have hZ0 := (gc8_Z0_pos GΛ β Jghost).le
  positivity


variable {ι : Type*} [DecidableEq ι] [Fintype ι]


theorem gc8_core_delta_supported_allConn (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  (gc8_crossingAllConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet).2.2.2


theorem gc8_core_crossing_forces_oneCluster (ends : ι → Sym2 V) (K : Finset ι) {o x y g w : V}
    (hox : connK ends K o x) (hyg : connK ends K y g)
    (hwo : connK ends K w o) (hwy : connK ends K w y) :
    connK ends K o x ∧ connK ends K o y ∧ connK ends K o g :=
  gc7_core_crossing_forces_oneCluster ends K hox hyg hwo hwy


theorem gc8_core_delta_lower_bound_ghost (β : ℝ) (J : Sym2 (Option V) → ℝ) (A : Finset (Option V))
    (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
    eΛ * Sharpness.currentSum (withGhost G) β J A
        ≥ (Sharpness.expectationJ (withGhost G) β J A) ^ 2 * Sharpness.currentSum (withGhost G) β J ∅
      ∧ 0 ≤ (Sharpness.expectationJ (withGhost G) β J A) ^ 2
          * Sharpness.currentSum (withGhost G) β J ∅ :=
  ⟨gc8_claim1_griffiths_step_ghost G β J A eΛ hβ hJ hgriff,
   mul_nonneg (sq_nonneg _) (gc8_Z0_pos G β J).le⟩


theorem gc8_core_delta_lower_bound_ghost_nonneg (β : ℝ) (J : Sym2 (Option V) → ℝ)
    (A : Finset (Option V)) (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
    0 ≤ eΛ * Sharpness.currentSum (withGhost G) β J A := by
  obtain ⟨hge, hnn⟩ := gc8_core_delta_lower_bound_ghost G β J A eΛ hβ hJ hgriff
  exact le_trans hnn hge


theorem gc8_core_pairSum_nonneg (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P : Finset ι → Prop) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ drd_pairSum ends A F P := by
  unfold drd_pairSum
  refine Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun K _ => ?_))
  exact mul_nonneg (hF m) (by split <;> norm_num)


theorem gc8_core_delta_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
  rw [gc8_core_delta_supported_allConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet]
  exact add_nonneg (gc8_core_pairSum_nonneg ends _ F _ hF) (gc8_core_pairSum_nonneg ends _ F _ hF)


end StatMech.Walls
