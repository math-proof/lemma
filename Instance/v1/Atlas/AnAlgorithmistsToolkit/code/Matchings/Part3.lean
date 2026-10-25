/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part3
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

noncomputable instance chainVertexFintype {n : ℕ} {G : BipartiteGraph n} :
    Fintype (ChainVertex G) :=
  inferInstanceAs (Fintype (SizedMatching G n ⊕ SizedMatching G (n - 1)))

instance chainVertexDecEq {n : ℕ} {G : BipartiteGraph n} :
    DecidableEq (ChainVertex G) :=
  inferInstanceAs (DecidableEq (SizedMatching G n ⊕ SizedMatching G (n - 1)))

end PartialMatching
end Matchings
