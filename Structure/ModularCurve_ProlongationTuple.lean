import Def.ModularCurve_GlueData
import Lemma.ModularCurve.SupersingularNodePlaces
import Lemma.ModularCurve.CoeffSemilinearAut
import Def.ModularCurve_AtkinLehnerPartial
import Lemma.ModularCurve.CuspidalClass
import Def.ModularCurve_X0ModL
import Lemma.ModularCurve.CharPReduction
import Structure.AlgebraicCurve_RegularProlongation
import Lemma.AlgebraicCurve.Repartitions
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

namespace ProlongationTuple

def atkinLehnerBar (N q : ℕ) [NeZero q] :
    modularFunctionFieldBar (N * q) ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar (N * q) :=
  geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)


end ProlongationTuple

set_option linter.unusedVariables false in

structure ProlongationTuple (P : PlaceSpecialization A q N data hKr k red hα hβ) where

  redBar : ResidueField A →+* k
  redBar_residue : ∀ a : A, redBar (IsLocalRing.residue A a) = red a

  ι : modularFunctionFieldFullC (ResidueField A) N →+* modularFunctionFieldC k N
  ι_coe : ∀ x : modularFunctionFieldFullC (ResidueField A) N,
    ((ι x : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffMap redBar (x : LaurentSeries (ResidueField A))

  R₁ : RegularProlongation A (modularFunctionFieldBar (N * q))
    (modularFunctionFieldFullC (ResidueField A) N)

  R₂ : RegularProlongation A (modularFunctionFieldBar (N * q))
    (modularFunctionFieldFullC (ResidueField A) N)

  residue₁_coeffMap : ∀ (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y

  mem_integersFst_iff : ∀ f : modularFunctionFieldBar (N * q),
    f ∈ R₁.integers ↔ (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red

  mem_integersSnd_iff : ∀ f : modularFunctionFieldBar (N * q),
    f ∈ R₂.integers ↔
      ((ProlongationTuple.atkinLehnerBar N q f : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red

  residue₂_eq : ∀ (f : modularFunctionFieldBar (N * q)) (h : f ∈ R₂.integers),
    R₂.residue ⟨f, h⟩ = R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q f,
      (mem_integersFst_iff (ProlongationTuple.atkinLehnerBar N q f)).mpr
        ((mem_integersSnd_iff f).mp h)⟩

  residue₁_eq_modularRedLocHom : ∀ (f : modularFunctionFieldBar (N * q))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
    ∃ h : f ∈ R₁.integers,
      ((ι (R₁.residue ⟨f, h⟩) : modularFunctionFieldC k N) : LaurentSeries k) =
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hf⟩

namespace ProlongationTuple

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)


def residue₁ : R.R₁.integers →+* modularFunctionFieldC k N := R.ι.comp R.R₁.residue

def residue₂ : R.R₂.integers →+* modularFunctionFieldC k N := R.ι.comp R.R₂.residue


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


set_option linter.unusedVariables false in

structure ExceptionalProlongations [PerfectField k] (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (m : ℕ) where

  Rex : Fin m → RegularProlongation A (modularFunctionFieldBar (N * q))
    (RatFunc (ResidueField A))

  unit_compat : ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
      (h₂ : f ∈ R.R₂.integers),
    R.residue₁ ⟨f, h₁⟩ ≠ 0 → R.residue₂ ⟨f, h₂⟩ ≠ 0 →
    w.ord (R.residue₁ ⟨f, h₁⟩) = 0 →
    (arithFrobC q k N • w).ord (R.residue₂ ⟨f, h₂⟩) = 0 →
    ∀ i : Fin m, ∃ h : f ∈ (Rex i).integers, (Rex i).residue ⟨f, h⟩ ≠ 0

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
