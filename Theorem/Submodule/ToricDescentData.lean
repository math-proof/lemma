module

public import Mathlib
public import Theorem.MvPolynomial.MazurPrincipleCore
public import Def.ModularCurve_DeligneRapoport
public import Theorem.LaurentSeries.HeckeOperator
public import Theorem.WeierstrassCurve.ConditionalCurrency
public import Structure.ModularCurve_ToricDescentData

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generic

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]


public theorem IsAbelianPartData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G}
    {𝒯 : Submodule HeckeAlg J} {δ : Fin 2 → J →+ J₀} (h : IsAbelianPartData S I 𝒯 δ) :
    IsAbelianPartDataQGuarded q S I 𝒯 δ where
  toric_le_ker := h.toric_le_ker
  goodPrime_equivariant := h.goodPrime_equivariant
  component_eisenstein := fun 𝔪 hmax heis _ => h.component_eisenstein 𝔪 hmax heis


public theorem toricFrobeniusSq (h : ExistsToricData q S I φ δ) : ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1


public theorem isAbelianPartData (h : ExistsToricData q S I φ δ) : IsAbelianPartData S I h.toric δ :=
  h.choose_spec.2

end ExistsToricData


public theorem ExistsToricData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
    {δ : Fin 2 → J →+ J₀} (h : ExistsToricData q S I φ δ) :
    ExistsToricDataQGuarded q S I φ δ := by
  obtain ⟨𝒯, hfrob, hab⟩ := h
  exact ⟨𝒯, hfrob, hab.qGuarded⟩

namespace ExistsToricDataQGuarded

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}


public theorem toricFrobeniusSq (h : ExistsToricDataQGuarded q S I φ δ) :
    ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1


public theorem isAbelianPartDataQGuarded (h : ExistsToricDataQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded q S I h.toric δ :=
  h.choose_spec.2

end ExistsToricDataQGuarded


public theorem toricFrobeniusSq (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusSq (q : ℕ) φ h.toric :=
  h.choose_spec.1


public theorem isAbelianPartDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded (q : ℕ) S I h.toric δ :=
  h.choose_spec.2.1


public theorem toricFrobeniusHecke (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusHecke q φ h.toric :=
  h.choose_spec.2.2


public theorem toExistsToricDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ExistsToricDataQGuarded (q : ℕ) S I φ δ :=
  ⟨h.toric, h.toricFrobeniusSq, h.isAbelianPartDataQGuarded⟩

end ExistsToricDataFullQGuarded

end Generic

section Degeneracy

variable (N q : ℕ) [NeZero N] [NeZero q]


public theorem degeneracyPushforwardInputs_intro
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ) :
    DegeneracyPushforwardInputs N q :=
  ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩


public theorem degeneracyPushforwardPair_eq
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ) :
    degeneracyPushforwardPair N q =
      ![Pic0.pushforwardAlongHom (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hfinα hNα,
        Pic0.pushforwardAlongHom (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hfinβ hNβ] := by
  rw [degeneracyPushforwardPair, dif_pos (degeneracyPushforwardInputs_intro hα hβ hfinα hNα hfinβ hNβ)]


public theorem degeneracyPushforwardPair_of_not (h : ¬ DegeneracyPushforwardInputs N q) :
    degeneracyPushforwardPair N q = 0 := by
  rw [degeneracyPushforwardPair, dif_neg h]

end Degeneracy

end ModularCurve

end
