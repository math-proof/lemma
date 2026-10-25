-- Carved from Lemma/Definitions/Def_ModularCurve_CuspSpace.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.CuspSpace

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

variable (N : ℕ)

namespace CuspSpace

variable {N}

variable (N)

instance instFinite [NeZero N] : Finite (CuspSpace N) :=
  Finite.of_surjective _ (fromCoset_surjective N)

instance instNonempty : Nonempty (CuspSpace N) := ⟨mk N ∞⟩

instance instSubsingletonOfOne : Subsingleton (CuspSpace 1) := by
  constructor
  rintro ⟨x⟩ ⟨y⟩
  obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
  obtain ⟨h, hh⟩ := OnePoint.exists_mem_SL2 ℤ y
  show mk 1 x = mk 1 y
  have hmem : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 1 := fun γ => by
    rw [Gamma0_mem]; exact Subsingleton.elim _ _
  rw [← hg, ← hh]
  symm
  rw [show (mapGL ℚ h • (∞ : OnePoint ℚ)) = mapGL ℚ (h * g⁻¹) • (mapGL ℚ g • (∞ : OnePoint ℚ))
    by rw [← mul_smul, ← map_mul, inv_mul_cancel_right]]
  exact mk_smul (hmem _) _

variable {N}

variable (N)

variable {N}

end CuspSpace

end

end ModularCurve

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

