/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part5
open scoped LinearAlgebra.Projectivization


noncomputable section

open MvPolynomial Finsupp

open scoped LinearAlgebra.Projectivization

namespace Theorem1324

variable {n : ℕ} (k : Type*) [Field k]


/-- Theorem 13.24. For any ideal $I \subseteq k[X_0, \ldots, X_n]$, the affine
piece $\{P \mid f(1, P) = 0 \,\forall f \in I\}$ equals the affine piece of
the projective closure of $I$ dehomogenized at $X_0$ and re-homogenized. -/
theorem projective_closure_of_affinePart_eq
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    {P : Fin n → k | ∀ f ∈ I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal
        (I.map (AffineParts.dehomogenize k 0)),
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·


    intro hP g hg

    have h13_23 := Theorem1323.projective_closure_cap_affine_eq k
      (I.map (AffineParts.dehomogenize k 0))
    have hP_affine : P ∈ {P : Fin n → k |
        ∀ f ∈ I.map (AffineParts.dehomogenize k 0), eval P f = 0} := by
      intro h hh

      have : I.map (AffineParts.dehomogenize k 0) ≤ RingHom.ker (eval P) := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        simp only [Ideal.mem_comap, RingHom.mem_ker]
        rw [Theorem1323.eval_dehomogenize_eq]
        exact hP f hf
      exact this hh
    exact (h13_23 ▸ hP_affine) g hg
  ·


    intro hP f hf
    rw [← Theorem1323.eval_homogenize_dehomogenize_eq k f P]
    exact hP _ (Theorem1323.homogenize_dehomogenize_mem_homogenizeIdeal k hf)

end Theorem1324

end

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial Finsupp

open scoped LinearAlgebra.Projectivization

namespace Corollary1326

variable {n : ℕ} (k : Type*) [Field k]

/-- Functoriality: equal subsets have equal vanishing ideals. -/
lemma vanishingIdeal_eq_of_set_eq (S T : Set (Fin n → k)) (h : S = T) :
    vanishingIdeal k S = vanishingIdeal k T :=
  congrArg (vanishingIdeal k) h

end Corollary1326
end
