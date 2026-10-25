/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
import Theorem.StatisticalMechanics.Code.FK.PlacementClose.Part2
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedSelectedLaws.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedSelectedLaws

open Lattice FK Percolation

open RevealmentConstruction WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedCoherentLimit

open FKSharpnessWeightedPhaseTransport

variable {d : Nat}


theorem coherentTranslatedLaw_covariant
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    (coherentTranslatedLaw mu y :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (coherentTranslatedLaw mu x :
        Measure (ConfigSpace (Sym2 (Site d)))).map
          (ConfigSpace.shift (Multiplicative.ofAdd (x - y))) := by
  unfold coherentTranslatedLaw
  change (mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-y))) =
    ((mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-x)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)))
  rw [Measure.map_map (ConfigSpace.measurable_shift _)
    (ConfigSpace.measurable_shift _)]
  congr 1
  rw [← ConfigSpace.shift_mul]
  apply congrArg (fun g : Multiplicative (Site d) =>
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
      ConfigSpace (Sym2 (Site d))))
  apply Multiplicative.toAdd.injective
  change -y = (x - y) + (-x)
  abel

end FKSharpnessWeightedSelectedLaws
end OSSS
end StatMech
