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
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part5
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def transitionEncoding {n : ℕ} {G : BipartiteGraph n} {T : Transition G}
    {s t : PerfMatching G} (data : TypeBPathData T s t) : ChainVertex G :=
  data.encodingVertex

def typeBUsesTransition {n : ℕ} {G : BipartiteGraph n}
    (T : Transition G) (s t : PerfMatching G) : Prop :=
  Nonempty (TypeBPathData T s t)

open Classical in

noncomputable def partner {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (v : ChainVertex G) : PerfMatching G :=
  match v with
  | Sum.inl s => s
  | Sum.inr m => augment m

noncomputable def partnerPreimage {n : ℕ} {G : BipartiteGraph n}
    (augment : SizedMatching G (n - 1) → PerfMatching G)
    (s : PerfMatching G) : Finset (ChainVertex G) :=
  Finset.univ.filter (fun v => partner augment v = s)

end PartialMatching
end Matchings
