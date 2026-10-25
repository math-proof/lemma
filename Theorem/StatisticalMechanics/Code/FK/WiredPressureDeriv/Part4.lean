/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxSecantData
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


variable {d : ℕ}


theorem wpd_wiredDensityUpperBound (N : ℕ)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
      atTop (𝓝 (g t)))
    (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
    fdd_WiredDensityUpperBound (d := d) N g := by
  intro e' t
  exact wpd_wiredAvgDensity_le_rightDeriv 2 (by norm_num) hE g hg hlim t _ (hcol e' t)


theorem wpd_fk_uniqueness (N : ℕ) (eb : Sym2 (boxVerts d N))
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hwiredlim : ∀ t,
      Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hwcol : wpd_AvgWiredDensityCollapse (d := d) N)
    (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
    (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fdd_fk_uniqueness_of_primitives N eb Gn hEfree hg hfree hcol hflc
    (wpd_wiredDensityUpperBound N hEbox g hg hwiredlim hwcol) hwrc


theorem wpd_fk_uniqueness_of_surfaceVolume (N : ℕ) (eb : Sym2 (boxVerts d N))
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hsv : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ))
      atTop (𝓝 0))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hwcol : wpd_AvgWiredDensityCollapse (d := d) N)
    (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
    (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  wpd_fk_uniqueness N eb Gn hEfree hEbox hg hfree
    (fun t => wpd_wiredTiltFreeEnergy_tendsto 2 (by norm_num) hEbox g t (hboxfree t) hsv)
    hcol hwcol hflc hwrc

end FK
end StatMech
