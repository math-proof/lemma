/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.NonnegDependence.Part2

@[expose] public section

open Finset Function


namespace NonnegDependence

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

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

end NonnegDependence
