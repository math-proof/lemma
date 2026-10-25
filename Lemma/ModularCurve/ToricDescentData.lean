import Mathlib
import Lemma.ModularCurve.MazurPrincipleCore
import Def.ModularCurve_DeligneRapoport
import Lemma.ModularCurve.HeckeOperator
import Lemma.Isogeny.ConditionalCurrency
import Structure.ModularCurve_ToricDescentData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generic

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]


theorem IsAbelianPartData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G}
    {𝒯 : Submodule HeckeAlg J} {δ : Fin 2 → J →+ J₀} (h : IsAbelianPartData S I 𝒯 δ) :
    IsAbelianPartDataQGuarded q S I 𝒯 δ where
  toric_le_ker := h.toric_le_ker
  goodPrime_equivariant := h.goodPrime_equivariant
  component_eisenstein := fun 𝔪 hmax heis _ => h.component_eisenstein 𝔪 hmax heis

def ExistsToricData (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartData S I 𝒯 δ

namespace ExistsToricData

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricData q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricData q S I φ δ) : ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartData (h : ExistsToricData q S I φ δ) : IsAbelianPartData S I h.toric δ :=
  h.choose_spec.2

end ExistsToricData

def ExistsToricDataQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartDataQGuarded q S I 𝒯 δ

theorem ExistsToricData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
    {δ : Fin 2 → J →+ J₀} (h : ExistsToricData q S I φ δ) :
    ExistsToricDataQGuarded q S I φ δ := by
  obtain ⟨𝒯, hfrob, hab⟩ := h
  exact ⟨𝒯, hfrob, hab.qGuarded⟩

namespace ExistsToricDataQGuarded

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricDataQGuarded q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricDataQGuarded q S I φ δ) :
    ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartDataQGuarded (h : ExistsToricDataQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded q S I h.toric δ :=
  h.choose_spec.2

end ExistsToricDataQGuarded

def ToricFrobeniusHecke (q : Nat.Primes) (φ : G) (𝒯 : Submodule HeckeAlg J) : Prop :=
  ∀ x ∈ 𝒯, φ • x = (((q : ℕ) : HeckeAlg) * heckeGen q) • x

def ExistsToricDataFullQGuarded (q : Nat.Primes) (S : Finset Nat.Primes) (I : Subgroup G)
    (φ : G) (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J,
    ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧ IsAbelianPartDataQGuarded (q : ℕ) S I 𝒯 δ ∧
    ToricFrobeniusHecke q φ 𝒯

namespace ExistsToricDataFullQGuarded

variable {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricDataFullQGuarded q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusSq (q : ℕ) φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded (q : ℕ) S I h.toric δ :=
  h.choose_spec.2.1

theorem toricFrobeniusHecke (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusHecke q φ h.toric :=
  h.choose_spec.2.2

theorem toExistsToricDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ExistsToricDataQGuarded (q : ℕ) S I φ δ :=
  ⟨h.toric, h.toricFrobeniusSq, h.isAbelianPartDataQGuarded⟩

end ExistsToricDataFullQGuarded

end Generic

section Degeneracy

variable (N q : ℕ) [NeZero N] [NeZero q]

def DegeneracyPushforwardInputs : Prop :=
  ∃ (_ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q)),
    NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα ∧
      NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ

open Classical in

def degeneracyPushforwardPair : Fin 2 → (JZero (N * q) →+ JZero N) :=
  if h : DegeneracyPushforwardInputs N q then
    ![Pic0.pushforwardAlongHom (heckeAlphaBar (AlgebraicClosure ℚ) N q) h.1 h.2.2.1 h.2.2.2.2.1,
      Pic0.pushforwardAlongHom (heckeBetaBar (AlgebraicClosure ℚ) N q) h.2.1 h.2.2.2.1 h.2.2.2.2.2]
  else 0

variable {N q}

theorem degeneracyPushforwardInputs_intro
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ) :
    DegeneracyPushforwardInputs N q :=
  ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩

theorem degeneracyPushforwardPair_eq
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

theorem degeneracyPushforwardPair_of_not (h : ¬ DegeneracyPushforwardInputs N q) :
    degeneracyPushforwardPair N q = 0 := by
  rw [degeneracyPushforwardPair, dif_neg h]

end Degeneracy

end ModularCurve

end
