import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.GluedPic0
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing

/--
[AlgebraicCurve_Place_hasValue_smul_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_hasValue_smul_iff.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {g : F}
  {a : K}
-- given
  (σ : F ≃ₐ[K] F) :
-- imply
  (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by
  have one : ∀ (τ : F ≃ₐ[K] F) (w : Place K F) (x : F), w.HasValue x a → (τ • w).HasValue (τ x) a := by
-- proof
    intro τ w x ⟨hx, hres⟩
    let e := Place.smulRingEquiv τ w.toValuationSubring
    have hmem : τ x ∈ (τ • w).toValuationSubring := (e ⟨x, hx⟩).2
    refine ⟨hmem, ?_⟩
    have hex : (⟨τ x, hmem⟩ : (τ • w).toValuationSubring) = e ⟨x, hx⟩ := Subtype.ext rfl
    have key : (Place.smulResidueAlgEquiv τ w) (residue w.toValuationSubring ⟨x, hx⟩) = residue (τ • w).toValuationSubring (e ⟨x, hx⟩) := by
      show IsLocalRing.ResidueField.mapEquiv _ (residue _ _) = residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    rw [hex, ← key, hres, AlgEquiv.commutes]
  refine ⟨fun h => ?_, one σ v g⟩
  have := one σ⁻¹ (σ • v) (σ g) h
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this


-- created on 2026-10-23
