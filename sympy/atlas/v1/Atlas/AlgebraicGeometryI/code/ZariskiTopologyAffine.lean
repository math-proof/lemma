/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiTopologyAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Basic

open MvPolynomial

noncomputable section

variable (k : Type*) [Field k] [IsAlgClosed k] (n : ℕ)

/-- Zariski-closed subset of `k^n` over an algebraically closed `k`: a set
cut out by the common vanishing of a (radical) ideal of polynomials
(cf. Thm 1.2 identifying closed sets with radical ideals). -/
def ZariskiClosed (S : Set (Fin n → k)) : Prop :=
  ∃ I : Ideal (MvPolynomial (Fin n) k), S = {p | ∀ f ∈ I, MvPolynomial.eval p f = 0}
