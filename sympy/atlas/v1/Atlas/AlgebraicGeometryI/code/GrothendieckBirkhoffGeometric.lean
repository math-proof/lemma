/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence

open BigOperators

namespace GBGeometric

/-- A vector bundle on `P^1` of positive rank, presented by its Grothendieck-Birkhoff
splitting `⊕ O(d_i)` with a decreasing tuple of integer degrees. -/
structure P1VectorBundle (k : Type*) [Field k] where
  rank : ℕ
  splittingType : Fin rank → ℤ
  sorted : ∀ i j : Fin rank, i ≤ j → splittingType j ≤ splittingType i
  hrank_pos : 0 < rank

/-- Total degree of `E = ⊕ O(d_i)` on `P^1`: `deg E = ∑ d_i`. -/
def P1VectorBundle.degree {k : Type*} [Field k] (E : P1VectorBundle k) : ℤ :=
  ∑ i, E.splittingType i

/-- Forget the positivity of the rank and recover the abstract `SplittingType` record. -/
def P1VectorBundle.toSplittingType {k : Type*} [Field k]
    (E : P1VectorBundle k) : GBExistence.SplittingType E.rank where
  degrees := E.splittingType
  sorted := E.sorted

/-- `k[x]` is a principal ideal domain (used to access the structure theorem on `P^1`). -/
instance polynomial_pid (k : Type*) [Field k] :
    IsPrincipalIdealRing (Polynomial k) :=
  inferInstance

set_option maxHeartbeats 400000 in

/-- Build a `P1VectorBundle` from an abstract splitting type once a positive-rank witness is given. -/
def splittingTypeToBundle (k : Type*) [Field k] {n : ℕ} (hn : 0 < n)
    (s : GBExistence.SplittingType n) : P1VectorBundle k where
  rank := n
  splittingType := s.degrees
  sorted := s.sorted
  hrank_pos := hn
