/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly1
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly2.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DetWalkExp


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Bucket

variable {L : ℕ} [NeZero L]


noncomputable def ons_bucketE (L : ℕ) [NeZero L] (x ω : ℂ) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
      (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmat L x ω) v


noncomputable def ons_bucketN (L : ℕ) [NeZero L] (x ω : ℂ) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmat L x ω) v


end Bucket
end StatMech.Onsager
