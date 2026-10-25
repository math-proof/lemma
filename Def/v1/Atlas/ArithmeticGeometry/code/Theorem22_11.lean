/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Lemma22_10
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


section Theorem22_11

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- Adèle-theoretic *index of speciality* of a divisor $D$: the difference
$g - 1 - r(D)$ between the genus and the Riemann defect at $D$. -/
noncomputable def adeleIndexOfSpeciality (D : P →₀ ℤ) : ℤ :=
  (genusVal_ax (F := F) (O := O) k : ℤ) - 1 -
    riemannDefect (F := F) (O := O) k D

/-- When $T = \top$ and $S \leq T$, the quotient $T / (T \cap S)$ is canonically
linearly equivalent to $M / S$. -/
noncomputable def quotientTopEquiv {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (hT : T = ⊤) (hST : S ≤ T) :
    (↥T ⧸ Submodule.comap T.subtype S) ≃ₗ[R] (M ⧸ S) := by
  subst hT
  exact (Submodule.Quotient.equiv _ S Submodule.topEquiv (by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨y, _⟩, hym, rfl⟩; exact hym
    · intro hx; exact ⟨⟨x, trivial⟩, hx, rfl⟩))

end Theorem22_11
