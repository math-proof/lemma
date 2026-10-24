/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Lemma26Lec10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.DisagreementStability
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.DisagreementStability
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames
import sympy.atlas.v1.Atlas.BooleanFunctions.code.UniqueGames

open Finset BigOperators

namespace BooleanFourier

noncomputable def vertexAvgFunc {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGames.UniqueGame V W k) (f : W → (Fin k → Bool) → ℝ) (v : V) :
    (Fin k → Bool) → ℝ :=
  fun x => (1 / (game.left_degree : ℝ)) *
    ∑ e ∈ game.edges.filter (fun e => e.1 = v),
      f e.2 (x ∘ (game.constraint v e.2 : Equiv.Perm (Fin k)).symm)
