/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000


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
