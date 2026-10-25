/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part2
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


noncomputable def freeDomainTranslateEquiv {d : Nat}
    (g : Multiplicative (Site d)) (K : Finset (Site d)) :
    freeDomainVertices K ≃ freeDomainVertices (K.image fun x => g • x) :=
  iptp_transInteriorEquiv g K

end StatMech.FrontierB
