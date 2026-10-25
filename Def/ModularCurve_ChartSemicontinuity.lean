import Def.ModularCurve_ProlongationTuple
import Def.ModularCurve_FibreModel
import Mathlib.Algebra.Polynomial.Derivative
import Structure.ModularCurve_ChartSemicontinuity

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

def ReducesDivisors (P : PlaceSpecialization A q N data hKr k red hα hβ) : Prop :=
  ∀ (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries
      (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ∈ modularFunctionFieldC k N),
    CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ V, D V = V.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        Finsupp.mapDomain P.sp D v =
          v.ord (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
            hmem⟩ : modularFunctionFieldC k N)

def LocalSemicontinuity : Prop :=
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
        (∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ u : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) ≠ u →
        (∀ W, P.IsStrictSnd W → P.reduceSnd W = u → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceSnd (P.sndDiv D) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩))

noncomputable def fibreReduction (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries
      (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ∈ modularFunctionFieldC k N) :
    modularFunctionFieldC k N :=
  ⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩, hmem⟩

omit R in

noncomputable def chartClosure (S : Set (modularFunctionFieldBar (N * q))) :
    Subring (modularFunctionFieldBar (N * q)) :=
  Subring.closure S

def chartLocalSetFst (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Set (modularFunctionFieldBar (N * q)) :=
  {f | ∃ (g u : modularFunctionFieldBar (N * q)) (_ : g ∈ chartClosure S) (_ : u ∈ chartClosure S)
      (hu₁ : u ∈ R.R₁.integers),
      ¬ v.HasValue (R.residue₁ ⟨u, hu₁⟩) (0 : k) ∧ f * u = g}


def HasCharts : Prop :=
  ∀ v : Place k (modularFunctionFieldC k N),
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
    ∃ S : Set (modularFunctionFieldBar (N * q)), IsChartAt R v S

def HasCoordinates (P : PlaceSpecialization A q N data hKr k red hα hβ) : Prop :=
  ∀ v : Place k (modularFunctionFieldC k N),
    ∃ (T : modularFunctionFieldBar N)
      (hT : (T : LaurentSeries
        (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
      (hmem : CharPReduction.modularRedLocHom N A.toSubring red ⟨T,
        hT⟩ ∈ modularFunctionFieldC k N),
      (∃ c : k, v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) c) = 1) ∧
      ∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u' = v →
        ∃ a : A, 0 < u'.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ∧
          0 < v.ord (fibreReduction T hT hmem - algebraMap k (modularFunctionFieldC k N) (red a))

end ModularCurve.PlaceSpecialization
