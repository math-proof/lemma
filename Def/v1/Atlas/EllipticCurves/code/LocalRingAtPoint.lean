/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/LocalRingAtPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.EllipticCurves.code.LocalRingAtPoint


namespace LocalRingAtPoint

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

variable (P : LocalRingAtPoint k K)

/-- The local ring at a point of a smooth curve is a principal ideal domain (part of
Definition 23.3). -/
noncomputable def maximalIdeal : Ideal P.toValuationSubring :=
  IsLocalRing.maximalIdeal P.toValuationSubring

/-- An element $u \in \mathcal{O}_P$ is a uniformizer at $P$ if it generates the maximal
ideal $\mathfrak{m}_P = (u)$ (Definition 23.3). -/
def IsUniformizerAt (u : P.toValuationSubring) : Prop :=
  P.maximalIdeal = Ideal.span {u}

/-- A rational function $g \in K$ is regular at $P$ if it lies in the local ring $\mathcal{O}_P$. -/
def IsRegularAt (g : K) : Prop :=
  g ∈ P.toValuationSubring

/-- An element $u$ of a local ring is a uniformizer if it generates the maximal ideal. -/
def IsUniformizer {R : Type*} [CommRing R] [IsLocalRing R] (u : R) : Prop :=
  IsLocalRing.maximalIdeal R = Ideal.span {u}

end LocalRingAtPoint
