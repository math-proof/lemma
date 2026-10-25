/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part2
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

noncomputable def PeriodicGraph.shiftedFreeMultiMass
    (P : PeriodicGraph V) (z : Site 2) (N : Nat)
    (t : Finset (Sym2 (P.BufferedVertex N)))
    (p q : Real) (m : Nat) (hNm : N ≤ m) : Real :=
  med_multiMassProb (fkProb (P.shiftedBufferedGraph z m) p q)
    ((t.image (Sym2.map (P.bufferedVertexInclLE hNm))).image
      (Sym2.map (P.shiftBufferedEquiv z m)))

end StatMech.FK.PeriodicPlanar
