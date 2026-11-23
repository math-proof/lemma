/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000

public section

noncomputable section

/-- Commutativity of partial derivatives on $\mathbb{R}[x_0, x_1]$:
$\partial_i \partial_j f = \partial_j \partial_i f$. -/
lemma pderiv_comm_poly (i j : Fin 2) (f : Poly2) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp [MvPolynomial.pderiv_X, Derivation.leibniz]
    rw [hp]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Pi.single, Function.update] <;> ring


end
