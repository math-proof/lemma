/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset Function

namespace NonnegDependence

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- A bipartite matching between $X$ and $Y$: a finite set of edges $(x, y)$ such that no two edges share a left endpoint or a right endpoint. -/
structure Matching (X Y : Type*) [DecidableEq X] [DecidableEq Y] where
  edges : Finset (X × Y)
  left_inj : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.1 = e₂.1 → e₁ = e₂
  right_inj : ∀ ⦃e₁ e₂⦄, e₁ ∈ edges → e₂ ∈ edges → e₁.2 = e₂.2 → e₁ = e₂

/-- Decidable equality on matchings reduces to decidable equality on their underlying edge sets. -/
instance : DecidableEq (Matching X Y) := by
  intro a b; cases a; cases b; simp only [Matching.mk.injEq]; exact inferInstance

/-- The set of left endpoints covered by the matching $F$. -/
def Matching.leftVerts (F : Matching X Y) : Finset X := F.edges.image Prod.fst

/-- The set of right endpoints covered by the matching $F$. -/
def Matching.rightVerts (F : Matching X Y) : Finset Y := F.edges.image Prod.snd

/-- The injection $f : X \hookrightarrow Y$ extends the matching $F$ if $f(x) = y$ for every edge $(x, y) \in F$. -/
def extendsMatching (f : X ↪ Y) (F : Matching X Y) : Prop :=
  ∀ e ∈ F.edges, f e.1 = e.2

/-- Decidability of `extendsMatching`, by reducing to a finite conjunction over the edges of `F`. -/
instance decidableExtendsMatching (f : X ↪ Y) (F : Matching X Y) :
    Decidable (extendsMatching f F) :=
  inferInstanceAs (Decidable (∀ e ∈ F.edges, f e.1 = e.2))

/-- Injections $f : X \hookrightarrow Y$ that extend $T$ and avoid every matching in `Fs`. -/
noncomputable def matchingsAvoiding (T : Matching X Y) (Fs : List (Matching X Y)) :
    Finset (X ↪ Y) :=
  Finset.univ.filter (fun f => extendsMatching f T ∧ ∀ G ∈ Fs, ¬extendsMatching f G)

/-- Injections $f : X \hookrightarrow Y$ that avoid every matching in `Fs`, with no further extension constraint. -/
noncomputable def avoidsAllSet (Fs : List (Matching X Y)) : Finset (X ↪ Y) :=
  Finset.univ.filter (fun f => ∀ G ∈ Fs, ¬extendsMatching f G)

/-- Postcomposition of an injection $f : X \hookrightarrow Y$ with a permutation $\sigma$ of $Y$, yielding the injection $x \mapsto \sigma(f(x))$. -/
def compPerm (σ : Equiv.Perm Y) (f : X ↪ Y) : X ↪ Y :=
  f.trans σ.toEmbedding
