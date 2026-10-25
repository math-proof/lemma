/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- Reflexivity: any homogeneous representative is equivalent to itself on $X$. -/
theorem HomogeneousRep.equivOn_refl (r : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) :
    r.equivOn k r X := by
  intro P _
  simp [sub_self]

/-- Symmetry of `equivOn`: if $r_1 \sim r_2$ on $X$ then $r_2 \sim r_1$ on $X$. -/
theorem HomogeneousRep.equivOn_symm (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k)))
    (h : r₁.equivOn k r₂ X) :
    r₂.equivOn k r₁ X := by
  intro P hP
  have hval := h P hP
  simp only [map_sub, map_mul] at hval ⊢
  have := neg_eq_zero.mpr hval
  rw [neg_sub] at this
  exact this

end ProjectiveRegularFunction
end
