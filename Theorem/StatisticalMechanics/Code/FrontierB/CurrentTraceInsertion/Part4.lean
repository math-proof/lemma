/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion.Part4
open MeasureTheory
open scoped ENNReal BigOperators symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hasLatticeFiniteEnergyMerge_of_singleOpen
    {d : ℕ} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hone : ∀ e : Sym2 (Site d), e ∈ (hypercubicLattice d).edgeSet →
      mu.map (setOpen e) ≪ mu) :
    HasLatticeFiniteEnergyMerge mu := by
  intro F hF
  induction F using Finset.induction with
  | empty =>
      have hempty : StatMech.Percolation.forceOpenFinset
          (∅ : Finset (Sym2 (Site d))) = id := by
        funext omega x
        simp [StatMech.Percolation.forceOpenFinset]
      rw [hempty, Measure.map_id]
  | @insert e F he ih =>
      have heL : e ∈ (hypercubicLattice d).edgeSet := hF (by simp)
      have hFL : (↑F : Set (Sym2 (Site d))) ⊆
          (hypercubicLattice d).edgeSet := by
        intro f hf
        exact hF (by simp [hf])
      have hmap := (ih hFL).map (StatMech.FK.measurable_setOpen e)
      have htrans := hmap.trans (hone e heL)
      rw [Measure.map_map (StatMech.FK.measurable_setOpen e)
        (StatMech.Percolation.measurable_forceOpenFinset F)] at htrans
      rwa [← StatMech.FK.forceOpenFinset_insert e F] at htrans

theorem freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

theorem freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

theorem plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

end StatMech.FrontierB
