/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Def.StatisticalMechanics.Code.Universality.HexBridge.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexContourEmb

variable {W I : Type*} (E : HexContourEmb W I)


theorem summable_of_summable (hZ : Summable E.wtSAW) : Summable E.wtContour :=
  hZ.comp_injective E.emb_inj


theorem not_summable_of_not_summable (hI : ¬ Summable E.wtContour) :
    ¬ Summable E.wtSAW :=
  fun hZ => hI (E.summable_of_summable hZ)


theorem tsum_le (hZ : Summable E.wtSAW) :
    (∑' i, E.wtContour i) ≤ ∑' w, E.wtSAW w :=
  Summable.tsum_le_tsum_of_inj E.emb E.emb_inj (fun c _ => E.wtSAW_nn c)
    (fun _ => le_refl _) (E.summable_of_summable hZ) hZ

end HexContourEmb
end StatMech.Universality
