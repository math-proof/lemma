/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part2
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shk_connectedWithin_shift_iff (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d))
    (x y : S) :
    ConnectedWithin d (ConfigSpace.shift g omega)
        (shk_translateFinset g S : Set (Site d))
        ⟨g • (x : Site d), by exact (shk_mem_translateFinset_smul g S x).2 x.2⟩
        ⟨g • (y : Site d), by exact (shk_mem_translateFinset_smul g S y).2 y.2⟩ ↔
      ConnectedWithin d omega (S : Set (Site d)) x y := by
  simpa only [ConnectedWithin, shk_translateInduceIso] using
    ((shk_translateInduceIso g omega S).reachable_iff (u := x) (v := y))


theorem shk_shift_preimage_connWithinEvent (g : Multiplicative (Site d))
    (S : Finset (Site d)) (u x : Site d) (hu : u ∈ S) (hx : x ∈ S) :
    (ConfigSpace.shift g) ⁻¹'
        connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x) =
      connWithinEvent d (S : Set (Site d)) u x := by
  ext omega
  constructor
  · rintro ⟨_, _, hconn⟩
    exact ⟨hu, hx, (shk_connectedWithin_shift_iff g omega S
      ⟨u, hu⟩ ⟨x, hx⟩).1 hconn⟩
  · rintro ⟨_, _, hconn⟩
    exact ⟨(shk_mem_translateFinset_smul g S u).2 hu,
      (shk_mem_translateFinset_smul g S x).2 hx,
      (shk_connectedWithin_shift_iff g omega S ⟨u, hu⟩ ⟨x, hx⟩).2 hconn⟩


theorem shk_connWithinEvent_prob_translate (p : ℝ≥0) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (u x : Site d) (hu : u ∈ S) (hx : x ∈ S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x)) =
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (S : Set (Site d)) u x) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  have hmeas : MeasurableSet
      (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x)) := by
    apply measurableSet_of_dependsOn
    exact shp_connWithinEvent_dependsOn
  have hpres := (bernoulli_translationInvariant (E := Sym2 (Site d))
    (G := Multiplicative (Site d)) p hp) g
  have hpre := hpres.measureReal_preimage hmeas.nullMeasurableSet
  rw [shk_shift_preimage_connWithinEvent g S u x hu hx] at hpre
  exact hpre.symm


end Sharpness
end StatMech
