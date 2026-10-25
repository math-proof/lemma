/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Sampling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.Sampling
set_option maxHeartbeats 400000

open Finset Nat


namespace Sampling

variable {n : ℕ}

/-- Decidability of `ContainsTetrahedron`, exploited for the finite case-check used in
Lemma 2.4.3. -/
instance (H : Finset (Finset (Fin 5))) : Decidable (ContainsTetrahedron H) := by
  unfold ContainsTetrahedron; infer_instance

/-- Decidability of `IsTetrahedronFree5`. -/
instance (H : Finset (Finset (Fin 5))) : Decidable (IsTetrahedronFree5 H) := by
  unfold IsTetrahedronFree5; infer_instance

end Sampling
