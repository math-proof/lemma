/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc9Znormaliserpos
import Theorem.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc9deltadef
import Theorem.StatisticalMechanics.Code.Walls.gc9Jnonneg
import Theorem.StatisticalMechanics.Code.Walls.gc9betaderivcov3
import Theorem.StatisticalMechanics.Code.Walls.gc9switching
import Theorem.StatisticalMechanics.Code.Walls.gc9eq15insertion
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc9core.Part3
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.GhostCurrentRep

open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum sourcePairDisconnSum_eq_edgecopy)

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc9_core_ursell_nonpos_of_eq20 (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
    (x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hidxy := hid x y hox hoy hxy
  have hZ : 0 < gc9_Z_normaliser G β J' := gc9_Z_normaliser_pos G β J'
  have hD : 0 ≤ gc9_assembledD_pair ends F J o g x y :=
    gc9_assembledD_pair_nonneg ends F J o g x y hJ hF
  have hu : eg_ursell3 G β h o x y
      = - gc9_assembledD_pair ends F J o g x y / gc9_Z_normaliser G β J' := by
    rw [eq_div_iff (ne_of_gt hZ)]; linarith [hidxy]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le


theorem gc9_core_signDominance_of_eq20 (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    GHSSignDominance G β h o :=
  fun x y hox hoy hxy =>
    gc9_core_ursell_nonpos_of_eq20 G β h o g J' ends F J hJ hF hid x y hox hoy hxy


theorem gc9_core_ursell_nonpos_all_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc5_core_ursell_nonpos_of_signDominance G β h hβ hh o
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid) x y


theorem gc9_core_ghs_concavity_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    GHSThreePointSym G β h o :=
  gc5_core_ghs_concavity_of_signDominance G β h hβ hh o
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid)


theorem gc9_core_sharpness_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V) (Jc : ℝ)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc5_core_aizenman_barsky_of_signDominance G β h hβ hh o Jc
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid) hfactor


theorem gc9_eq20_specific_pins_bridge (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    gc8_PivotalSignBridge G β h o := by
  intro x y hox hoy hxy
  exact ⟨gc9_assembledD_pair ends F J o g x y, gc9_Z_normaliser G β J',
    gc9_assembledD_pair_nonneg ends F J o g x y hJ hF,
    gc9_Z_normaliser_pos G β J',
    hid x y hox hoy hxy⟩


theorem gc9_eq20_not_circular {u3 Z' D : ℝ} (hZ : 0 < Z') (hD : 0 ≤ D) (hid : u3 * Z' = -D) :
    u3 ≤ 0 := by
  have hu : u3 = - D / Z' := by rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le


theorem gc9_core_normaliser_nonvacuous :
    0 < gc9_Z_normaliser (⊤ : SimpleGraph (Fin 3)) 1 (ghostCoupling 1 1 (fun _ => 1)) :=
  gc9_Z_normaliser_pos_nonvacuous


theorem gc9_core_pivotalMass_nonvacuous :
    0 ≤ gc9_assembledD_pair (witEnds : Fin 2 → Sym2 (Fin 4)) (fun _ => 1) (fun _ => 1)
          (0 : Fin 4) 3 1 2 :=
  gc9_assembledD_pair_nonneg witEnds (fun _ => 1) (fun _ => 1) 0 3 1 2
    (fun _ => by norm_num) (fun _ => by norm_num)

end StatMech.Walls
