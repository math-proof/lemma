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
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part3
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

instance sizedMatchingDecEq {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    DecidableEq (SizedMatching G k) := by
  intro a b
  have h : a = b ↔ a.edges = b.edges := by
    constructor
    · intro h; subst h; rfl
    · intro h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h
  rw [h]; exact inferInstance

noncomputable instance sizedMatchingFintype {n : ℕ} {G : BipartiteGraph n} {k : ℕ} :
    Fintype (SizedMatching G k) :=
  Fintype.ofInjective SizedMatching.edges (by
    intro a b h; cases a; cases b; simp only [SizedMatching.mk.injEq] at h ⊢; exact h)

end PartialMatching
end Matchings
