/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalFixedBucketE
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (d : ons_Dart L) (r : ℕ) (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (r + 1) → ons_Dart L ↦
        (∃ k, loop k = d) ∧ ¬ ∃ k, loop k = ons_dartRev L d),
    if ons_decLoopExponent L loop = m then
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop
    else 0

noncomputable def ons_decFormalFixedBucketN
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (d : ons_Dart L) (r : ℕ) (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (r + 1) → ons_Dart L ↦
        (¬ ∃ k, loop k = d) ∧ ¬ ∃ k, loop k = ons_dartRev L d),
    if ons_decLoopExponent L loop = m then
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop
    else 0

end StatMech.Onsager
