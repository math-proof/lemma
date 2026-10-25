import Mathlib
import sympy.Basic
import Def.GaloisRep_Flat
import Lemma.Int.P2MUtil

open GaloisRepAdic

/--
[GaloisRepAdic_isFlatAt_of_isEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isFlatAt_of_isEquiv.lean)
-/

private lemma  isFlatAt_of_isEquiv
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsFlatAt p) : ρ₂.IsFlatAt p := by
  obtain ⟨e⟩ := e
  refine ⟨h.1, fun I hI => ?_⟩
  obtain ⟨H, _, _, hfin, hflat, hcocomm, eH, hmul, hgal⟩ := h.2 I hI

  have hmap : (I • (⊤ : Submodule A ρ₁.V)).map (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) =
      I • (⊤ : Submodule A ρ₂.V) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

  let E : (ρ₁.V ⧸ (I • (⊤ : Submodule A ρ₁.V))) ≃ₗ[A] (ρ₂.V ⧸ (I • (⊤ : Submodule A ρ₂.V))) :=
    Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap

  have hE : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x : ρ₁.V ⧸ (I • (⊤ : Submodule A ρ₁.V))),
      E (ρ₁.levelAction I σ x) = ρ₂.levelAction I σ (E x) := fun σ x =>
    Submodule.Quotient.induction_on _ x fun v =>
      congrArg (Submodule.Quotient.mk (p := I • (⊤ : Submodule A ρ₂.V))) (e.map_apply σ v)
  refine ⟨H, _, _, hfin, hflat, hcocomm, eH.trans E.toEquiv, fun f g => ?_, fun σ f g hfg => ?_⟩
  · change E (eH (f * g)) = E (eH f) + E (eH g)
    rw [hmul, map_add]
  · change E (eH g) = ρ₂.levelAction I σ (E (eH f))
    rw [hgal σ f g hfg, hE]
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ₁ ρ₂ : GaloisRepAdic A}
  {e : ρ₁.IsEquiv ρ₂}
  {p : ℕ}
-- given
  (h : ρ₁.IsFlatAt p) :
-- imply
  ρ₂.IsFlatAt p :=
-- proof
  isFlatAt_of_isEquiv e h


-- created on 2026-10-23
