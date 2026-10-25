/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.axisSwap_isErgodic
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hErgodic : P.IsErgodic mu) : P.axisSwap.IsErgodic mu := by
  refine ⟨P.axisSwap_isTranslationInvariant mu hErgodic.1, ?_⟩
  intro s hs hinvariant
  apply hErgodic.2 s hs
  intro z
  have h := hinvariant (siteAxisSwap z)
  change P.configTranslate (siteAxisSwap (siteAxisSwap z)) ⁻¹' s = s at h
  simpa using h


theorem PeriodicGraph.axisNeg_isErgodic
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hErgodic : P.IsErgodic mu) : P.axisNeg.IsErgodic mu := by
  refine ⟨P.axisNeg_isTranslationInvariant mu hErgodic.1, ?_⟩
  intro s hs hinvariant
  apply hErgodic.2 s hs
  intro z
  have h := hinvariant (siteNeg z)
  change P.configTranslate (siteNeg (siteNeg z)) ⁻¹' s = s at h
  simpa using h


end StatMech.FK.PeriodicPlanar
