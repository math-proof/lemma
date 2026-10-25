/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleurselleq
import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleprob
import Theorem.StatisticalMechanics.Code.Walls.gc5_bracketsign
import Theorem.StatisticalMechanics.Code.Walls.gc5_eqswi
import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc5_core_ensemble_ursell_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Ising.Current V))
    (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y :=
  egh_ensemble_ursell_eq G β J M B hox hoy hxy


theorem gc5_core_ensemble_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  egh_ensemble_prob_le_one G β J hβ hJ M B o x y


theorem gc5_core_bracket_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y
      ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  egh_u3_nonpos_bound G β J hβ hJ M B o x y μ hμ


theorem gc5_core_u3_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Ising.Current V)) (B : Finset V) (o x y : V) {μ : ℝ} (hμ : 0 ≤ μ) :
    -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  (gc5_core_bracket_sign G β J hβ hJ M B o x y hμ).2


theorem gc5_core_ursell_eq_lebowitz_plus_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = gc_lebowitzU4 G β h o x y
        + 2 * isingExpectation G β h (fun s => spin s o)
            * isingExpectation G β h (fun s => spin s x)
            * isingExpectation G β h (fun s => spin s y) :=
  gc_ursell_eq_lebowitz_plus_triple G β h o x y


theorem gc5_core_lebowitz_le_ursell (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    gc_lebowitzU4 G β h o x y ≤ eg_ursell3 G β h o x y :=
  gc_lebowitz_le_ursell G β h hβ hh o x y


theorem gc5_core_ursell_nonpos_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y


theorem gc5_core_ghs_concavity_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) :
    GHSThreePointSym G β h o :=
  gc_ghs_concavity_of_signDominance G β h hβ hh o hsd


theorem gc5_core_aizenman_barsky_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (J : ℝ) (hsd : GHSSignDominance G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor


end StatMech.Walls
