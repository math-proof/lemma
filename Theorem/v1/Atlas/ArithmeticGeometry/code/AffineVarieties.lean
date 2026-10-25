/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part2
variable (k : Type*) [Field k]


/-- For polynomials over $\overline{k}$, the ring-evaluation `MvPolynomial.eval` agrees with
the algebra-evaluation `MvPolynomial.aeval`. -/
lemma eval_eq_aeval_algebraicClosure {n : ℕ} (P : AffineSpace_k k n)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    MvPolynomial.eval P f = MvPolynomial.aeval P f := by
  unfold MvPolynomial.aeval MvPolynomial.eval
  simp [AlgHom.coe_mk]

/-- The algebraic set cut out by an ideal $I \subseteq \overline{k}[x_1, \ldots, x_n]$ is
the same as the Mathlib `zeroLocus` of $I$. -/
lemma algebraicSet_ideal_eq_zeroLocus {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    AlgebraicSet k n (I : Set _) =
      MvPolynomial.zeroLocus (AlgebraicClosure k) I := by
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, MvPolynomial.mem_zeroLocus_iff]
  exact forall₂_congr fun f _ => by rw [eval_eq_aeval_algebraicClosure]

