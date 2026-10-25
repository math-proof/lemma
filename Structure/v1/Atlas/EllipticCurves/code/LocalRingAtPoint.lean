/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/LocalRingAtPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


/-- An abstract local ring at a point $P$ of a curve $C/k$ with function field $K = k(C)$:
the ring of regular functions $\mathcal{O}_P = \{f \in k(C) : f(P) \neq \infty\}$ presented
as a valuation subring of $K$ whose valuation is nontrivial and trivial on the constants $k$
(Definition 23.3). -/
structure LocalRingAtPoint (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] where
  toValuationSubring : ValuationSubring K
  valuation_nontrivial : toValuationSubring.valuation.IsNontrivial
  valuation_trivial_on_k : ∀ (a : k), a ≠ 0 →
    toValuationSubring.valuation (algebraMap k K a) = 1

