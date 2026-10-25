import Mathlib
import Def.ModularCurve_LevelOneGlueData
import Lemma.ModularCurve.SupersingularNodes
import Def.ModularCurve_SupersingularModuli
import Structure.AlgebraicCurve_RegularProlongation
import Lemma.ModularCurve.CharPReduction
import Lemma.ModularCurve.CuspidalClass
import Def.ModularCurve_X0ModL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 400000 in

structure LevelOneProlongationPair (P : PlaceSpecialization A q 1 data hKr k red hα hβ) where

  redBar : ResidueField A →+* k
  redBar_residue : ∀ a : A, redBar (IsLocalRing.residue A a) = red a

  ι : modularFunctionFieldFullC (ResidueField A) 1 →+* modularFunctionFieldC k 1
  ι_coe : ∀ x : modularFunctionFieldFullC (ResidueField A) 1,
    ((ι x : modularFunctionFieldC k 1) : LaurentSeries k) = coeffMap redBar (x : LaurentSeries (ResidueField A))

  R₁ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  R₂ : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1)

  residue₁_coeffMap : ∀ (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q)),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * q)) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y

  mem_integers₂_iff : ∀ f : modularFunctionFieldBar (1 * q),
    f ∈ R₂.integers ↔ frickeInvolutionBar (1 * q) f ∈ R₁.integers

  residue₂_eq : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R₂.integers),
    R₂.residue ⟨f, h⟩ = R₁.residue ⟨frickeInvolutionBar (1 * q) f, (mem_integers₂_iff f).mp h⟩

  residue₁_eq_modularRedLocHom : ∀ (f : modularFunctionFieldBar (1 * q))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
    ∃ h : f ∈ R₁.integers,
      ((ι (R₁.residue ⟨f, h⟩) : modularFunctionFieldC k 1) : LaurentSeries k) =
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨f, hf⟩

end PlaceSpecialization

end ModularCurve
