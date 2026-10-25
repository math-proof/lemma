/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable instance sctTranslatedBoxFintype (d n : ℕ) (y : Site d) :
    Fintype {z : Site d // z ∈ sctTranslatedBox d n y} :=
  ((box_finite d n).image (fun z : Site d => z - y)).fintype

noncomputable instance sctTranslatedBoxGraphDecidableAdj (d n : ℕ) (y : Site d) :
    DecidableRel (sctTranslatedBoxGraph d n y).Adj := Classical.decRel _


end Sharpness
end StatMech
