/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GBSplittingUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GBSplittingExistence
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GBSplittingExistence
import Mathlib.Data.Multiset.Basic

open BigOperators

namespace GBUniqueness

/-- Sum of `h^0` dimensions across a multiset of twist degrees: for a multiset `s` of integers,
returns `∑_{d ∈ s} max(d + m + 1, 0)`, modeling the dimension of `H^0` of `⊕ O(d_i)(m)` on `P^1`. -/
def h0_multiset (s : Multiset ℤ) (m : ℤ) : ℕ :=
  (s.map (fun d => (d + m + 1).toNat)).sum

/-- Integer-valued variant of `h0_multiset`, summing `(d + m + 1).toNat` viewed as integers. -/
def h0z (s : Multiset ℤ) (m : ℤ) : ℤ :=
  (s.map (fun d => ((d + m + 1).toNat : ℤ))).sum

/-- Turn a tuple of degrees `degrees : Fin n → ℤ` into the corresponding multiset of values. -/
def degreesToMultiset {n : ℕ} (degrees : Fin n → ℤ) : Multiset ℤ :=
  Finset.univ.val.map degrees

/-- Multiset-level `h^1` formula: for splitting degrees `d_i`, the dimension of `H^1` of
`⊕ O(d_i)(m)` on `P^1` is `∑ max(-d_i - m - 1, 0)`. -/
def h1_multiset (s : Multiset ℤ) (m : ℤ) : ℕ :=
  (s.map (fun d => (-d - m - 1).toNat)).sum
