/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedSelectedLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
import Theorem.StatisticalMechanics.Code.FK.PlacementClose.Part2
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedSelectedLaws.Part2
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


noncomputable def coherentTranslatedLaw
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) (x : Site d) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨(mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-x))),
    inferInstance⟩

end FKSharpnessWeightedSelectedLaws
end OSSS
end StatMech
