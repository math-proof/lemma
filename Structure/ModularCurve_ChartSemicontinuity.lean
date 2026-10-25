import Structure.ModularCurve_ProlongationTuple
import Structure.ModularCurve_FibreModel
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)


def ChartEtaleAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop :=
  ∃ (z : modularFunctionFieldBar (N * q)) (m : Polynomial (modularFunctionFieldBar N)),
    z ∈ S ∧
    (∃ hz₂ : z ∈ R.R₂.integers, ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) ∧
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
    m.Monic ∧ m.natDegree = q + 1 ∧
    (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
    (∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure S) ∧
    ∀ h : (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
        ∈ R.R₁.integers,
      ¬ v.HasValue (R.residue₁ ⟨_, h⟩) (0 : k)

structure IsChartAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop where
  integral : ∀ s ∈ S, s ∈ R.R₁.integers
  regular : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
    (R.residue₁ ⟨s, integral s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring
  gens_affine : IsAffineGeomPlace k N v →
    heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ S ∧ heckeAlphaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N) ∈ S ∧
    heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ S ∧ heckeBetaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N) ∈ S
  gens_cusp : ¬ IsAffineGeomPlace k N v →
    heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)⁻¹ ∈ S ∧ heckeAlphaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N)⁻¹ ∈ S ∧
    heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)⁻¹ ∈ S ∧ heckeBetaBar
      (AlgebraicClosure ℚ) N q (CharPModel.jNBar N)⁻¹ ∈ S
  const_mem : ∀ a : A,
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ S
  nIncl : ∀ φ : modularFunctionFieldBar N,
    heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers →
    (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v →
      φ ∈ u₀.toValuationSubring) →
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ S) (e : modularFunctionFieldBar (N * q))
      (he : e ∈ S),
      ¬ v.HasValue (R.residue₁ ⟨e, integral e he⟩) (0 : k) ∧
        heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s
  valueLaw : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
    P.IsStrictFst W → P.reduceFst W = v →
      ∃ a : A, W.HasValue s (a : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨s, integral s hs⟩)
        (red a)
  separates : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.IsStrictSnd W → P.reduceFst W = v →
      ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ S),
        ¬ v.HasValue (R.residue₁ ⟨u, integral u hu⟩) (0 : k) ∧ 0 < W.ord u
  etale : ChartEtaleAt R v S
  dichotomy : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → P.IsStrictFst W ∨ P.IsStrictSnd W
  regularOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → s ∈ W.toValuationSubring


end ModularCurve.PlaceSpecialization
