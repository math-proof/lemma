module

public import Mathlib
public import Theorem.MvPolynomial.MazurPrincipleCore
public import Def.ModularCurve_DeligneRapoport
public import Def.ModularCurve_HeckeOperator
public import Def.AlgebraicCurve_ConditionalCurrency
public import Structure.ModularCurve_ToricDescentData

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generic

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]


def ExistsToricData (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartData S I 𝒯 δ

namespace ExistsToricData

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricData q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

end ExistsToricData

def ExistsToricDataQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartDataQGuarded q S I 𝒯 δ

namespace ExistsToricDataQGuarded

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricDataQGuarded q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

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

end Degeneracy

end ModularCurve

end
