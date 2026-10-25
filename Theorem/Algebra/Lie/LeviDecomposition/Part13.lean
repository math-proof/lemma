/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part12
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_lie_le_range_theta
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (hI : IsLieAbelian I)
    (f : leviHomScalarMaps (L := L) I) (hf : ∀ r : I, f.1 r = r) :
    (⁅I, (⊤ : LieSubmodule K L (leviHomScalarMaps I))⁆ :
        LieSubmodule K L (leviHomScalarMaps I)).toSubmodule ≤
      LinearMap.range (leviTheta I f) := by
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
  rw [Submodule.span_le]
  rintro g ⟨r, v, rfl⟩
  obtain ⟨a, ha⟩ := v.1.2
  refine ⟨a • r, ?_⟩
  apply Subtype.ext
  ext y
  change
    ((⁅((a • r).1 : L), (f.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L) =
      ((⁅(r.1 : L), (v.1.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L)
  rw [LieHom.lie_apply, LieHom.lie_apply]
  change
    ⁅(a • r : I).1, (f.1 y).1⁆ - (f.1 ⁅(a • r : I).1, y⁆).1 =
      ⁅r.1, (v.1.1 y).1⁆ - (v.1.1 ⁅r.1, y⁆).1
  have hry : ⁅r.1, y⁆ ∈ I := lie_mem_left K L I r.1 y r.2
  have hary : ⁅(a • r : I).1, y⁆ ∈ I :=
    lie_mem_left K L I (a • r).1 y (a • r).2
  have hrv : ⁅r.1, (v.1.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial r (v.1.1 y))
  have harf : ⁅(a • r : I).1, (f.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial (a • r) (f.1 y))
  rw [hrv, harf, zero_sub, zero_sub]
  have hv := congrArg Subtype.val (ha (⟨⁅r.1, y⁆, hry⟩ : I))
  have hfv := congrArg Subtype.val (hf (⟨⁅(a • r : I).1, y⁆, hary⟩ : I))
  rw [hv, hfv]
  simp only [SetLike.val_smul, smul_lie]

end LeviDecomposition
