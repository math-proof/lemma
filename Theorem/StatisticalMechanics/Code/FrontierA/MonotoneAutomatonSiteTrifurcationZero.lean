/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteTrifurcationZero
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open Finset Filter Topology

open scoped ENNReal

variable {d : ℕ}

theorem measurableSet_siteCanonicalTrifurcationEvent (x : Site d) :
    MeasurableSet (SiteCanonicalTrifurcationEvent x) := by
  change MeasurableSet (siteToBond ⁻¹'
    {omega | IsCanonicalTrifurcation d omega x})
  exact measurable_siteToBond (ctp_measurableSet_isCanonicalTrifurcation x)

theorem siteCanonicalTrifurcation_shift (g : Multiplicative (Site d))
    (eta : ConfigSpace (Site d)) (x : Site d) :
    IsCanonicalTrifurcation d (siteToBond (shift g eta)) (g • x) ↔
      IsCanonicalTrifurcation d (siteToBond eta) x := by
  rw [siteToBond_shift, ctp_isCanonicalTrifurcation_shift]

theorem siteCanonicalTrifurcationProb_const
    (mu : Measure (ConfigSpace (Site d)))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (x : Site d) :
    mu (SiteCanonicalTrifurcationEvent x) =
      mu (SiteCanonicalTrifurcationEvent 0) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hgx : g • (0 : Site d) = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [g]
  have hpre : (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹'
      SiteCanonicalTrifurcationEvent x =
        SiteCanonicalTrifurcationEvent 0 := by
    ext eta
    simp only [Set.mem_preimage, SiteCanonicalTrifurcationEvent, Set.mem_setOf_eq]
    rw [← hgx, siteCanonicalTrifurcation_shift]
  calc
    mu (SiteCanonicalTrifurcationEvent x) =
        mu ((shift g) ⁻¹' SiteCanonicalTrifurcationEvent x) :=
      (hinv.measure_preimage g
        (measurableSet_siteCanonicalTrifurcationEvent x)).symm
    _ = mu (SiteCanonicalTrifurcationEvent 0) := by rw [hpre]

end StatMech.FrontierA
