module
public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Structure.v1.Atlas.ArithmeticGeometry.code.Morphisms


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- Rescaling identity for homogeneous polynomials:
$f(cv_0, \ldots, cv_n) = c^d \cdot f(v_0, \ldots, v_n)$, where $d$ is the
homogeneous degree of $f$. -/
lemma homog_eval_rescale (n : ℕ) (f : HomogPoly k n)
    (c : AlgebraicClosure k) (v : Fin (n + 1) → AlgebraicClosure k) :
    eval (fun i => c * v i) f.poly = c ^ f.deg * eval v f.poly := by
  have := HomogeneousPolynomial.isHomogeneous_eval_smul f.poly f.deg f.isHomog c v
  exact this

end
