/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Def.StatisticalMechanics.Code.FK.FKDensityDeriv
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


theorem fdd_leftDeriv_le_wiredDensity (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
  (fdd_leftDeriv_le_freeDensity N Gn hE g hg hlim hcol e' t).trans
    (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t))


theorem fdd_wired_is_rightDeriv_of_upperBound_rightContinuous (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hub : fdd_WiredDensityUpperBound (d := d) N g)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hrc : ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t :=
  fdd_eq_rightDeriv_of_bracket_rightContinuous hg
    (fun s => fdd_leftDeriv_le_wiredDensity N Gn hE g hg hlim hcol e' s)
    (fun s => hub e' s) hrc


theorem fdd_IVDensityIsOneSidedDeriv_iff (N : ℕ) (g : ℝ → ℝ) :
    fpd_IVDensityIsOneSidedDeriv d N g
      ↔ fdd_WiredDensityIsRightDeriv (d := d) N g ∧ fdd_FreeDensityIsLeftDeriv (d := d) N g :=
  Iff.rfl


theorem fdd_IVDensityIsOneSidedDeriv_of_halves (N : ℕ) (g : ℝ → ℝ)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
    fpd_IVDensityIsOneSidedDeriv d N g :=
  ⟨hwired, hfree⟩


theorem fdd_fk_uniqueness (N : ℕ) (eb : Sym2 (boxVerts d N)) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpd_fk_uniqueness d N eb hg (fdd_IVDensityIsOneSidedDeriv_of_halves N g hwired hfree)


theorem fdd_fk_uniqueness_of_primitives (N : ℕ) (eb : Sym2 (boxVerts d N))
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
    (hwub : fdd_WiredDensityUpperBound (d := d) N g)
    (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fdd_fk_uniqueness N eb hg
    (fun e' t =>
      fdd_wired_is_rightDeriv_of_upperBound_rightContinuous N Gn hE hg hlim hcol hwub e' t
        (hwrc e' t))
    (fun e' t =>
      fdd_free_is_leftDeriv_of_leftContinuous N Gn hE g hg hlim hcol e' t (hflc e' t))


theorem fdd_halves_imp_fsc (N : ℕ) {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) (e' : Sym2 (boxVerts d N)) :
    fsc_FreeEnergyData d N e' :=
  fpd_densityDeriv_imp_fsc d N hg (fdd_IVDensityIsOneSidedDeriv_of_halves N g hwired hfree) e'

end FK
end StatMech
