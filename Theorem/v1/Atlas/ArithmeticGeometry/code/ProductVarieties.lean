module
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
public import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable (k : Type*) [Field k]


/-- If $P \in V$, then every polynomial vanishing on $V$ vanishes at $P$, i.e.
$I(V) \subseteq \ker(\mathrm{eval}_P)$. -/
lemma idealOfAlgebraicSet_le_ker_eval
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    idealOfAlgebraicSet V ≤ RingHom.ker (MvPolynomial.eval P) := by
  intro f hf
  rw [RingHom.mem_ker]
  exact hf P hP

