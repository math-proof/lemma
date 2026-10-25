import Mathlib
import Structure.ModularCurve_LevelOneProlongationPair
import Structure.AlgebraicCurve_SemistableCharts
import Lemma.ModularCurve.SpecializeModuli
import Def.ModularCurve_SupersingularModuli
import Lemma.ModularCurve.SupersingularNodePlaces

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ChartFst


end ChartFst

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}

namespace ChartFst

omit [DecidableEq (ResidueField ↥A)] in

end ChartFst

open Classical in

structure ChartFstLaws (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) : Prop where
  sheet_fixed : ∀ W ∈ S₁, frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst W)) = P.redFst W
  sheet_affine : ∀ W ∈ S₁, IsAffineGeomPlace (ResidueField ↥A) 1 (P.redFst W)
  sheet_not_mem_ssPlaces : ∀ W ∈ S₁, P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A)
  div_sheet : ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers), R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), (∀ W, D W = W.ord f) →
    ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr v) = v →
      IsAffineGeomPlace (ResidueField ↥A) 1 v → v ∉ ssPlaces p 1 (ResidueField ↥A) →
      Finsupp.mapDomain P.redFst (D.filter (· ∈ S₁)) v = v.ord (R.residue₁ ⟨f, h₁⟩)
  pw_sheet : ∀ W ∈ S₁, ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers),
    (∀ W' ∈ S₁, P.redFst W' = P.redFst W → f ∈ W'.toValuationSubring) →
    ∃ c : ↥A, W.HasValue f (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨f, h₁⟩) (IsLocalRing.residue ↥A c)

open Classical in

structure ChartFstSupply (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) : Prop where
  sheet : R.ChartFstLaws S₁
  exists_divisor : ∀ f : ↥(modularFunctionFieldBar (1 * p)), f ≠ 0 →
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), ∀ W, D W = W.ord f
  pw_strict : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))), P.IsStrictTypeOne W →
    ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers),
    (∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        P.IsStrictTypeOne W' → P.redFst W' = P.redFst W → f ∈ W'.toValuationSubring) →
    ∃ c : ↥A, W.HasValue f (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨f, h₁⟩) (IsLocalRing.residue ↥A c)
  pw_cusp : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))), P.IsInftySide W →
    ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers),
    (∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        P.IsInftySide W' → f ∈ W'.toValuationSubring) →
    ∃ c : ↥A, W.HasValue f (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨f, h₁⟩) (IsLocalRing.residue ↥A c)
  div_strict : ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers), R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), (∀ W, D W = W.ord f) →
    ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr v) ≠ v →
      Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) v = v.ord (R.residue₁ ⟨f, h₁⟩)
  div_cusp : ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (h₁ : f ∈ R.R₁.integers), R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), (∀ W, D W = W.ord f) →
      Finsupp.mapDomain P.redFst (D.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * p))) =
        (P.redFst (cuspInftyBar (1 * p))).ord (R.residue₁ ⟨f, h₁⟩)
  cusp_fixed : frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (P.redFst (cuspInftyBar (1 * p))))
    = P.redFst (cuspInftyBar (1 * p))
  redFst_eq_of_isInftySide : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
    P.IsInftySide W → P.redFst W = P.redFst (cuspInftyBar (1 * p))
  redFst_eq_charLGeomPlaceOfPoint_iff : ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (c₀ : ResidueField ↥A), P.redFst W = charLGeomPlaceOfPoint (ResidueField ↥A) c₀ ↔
      ∃ a : ↥A, IsLocalRing.residue ↥A a = c₀ ∧
        0 < W.ord (PlaceSpecialization.jFun (q := p)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))
  frob_charLGeomPlaceOfPoint : ∀ a : ResidueField ↥A,
    frobOnPlacesGeomLevel (ResidueField ↥A) 1 data hKr (charLGeomPlaceOfPoint (ResidueField ↥A) a)
      = charLGeomPlaceOfPoint (ResidueField ↥A) (a ^ p)
  pow_sq_eq_self_of_mem : ∀ a ∈ ssJSet p (ResidueField ↥A), a ^ (p ^ 2) = a
  isAffineGeomPlace_iff : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
    IsAffineGeomPlace (ResidueField ↥A) 1 v ↔ v ≠ P.redFst (cuspInftyBar (1 * p))
  mem_ssPlaces_iff : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
    v ∈ ssPlaces p 1 (ResidueField ↥A) ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = v
  isInftySide_cuspInftyBar : P.IsInftySide (cuspInftyBar (1 * p))


section Chart

variable (R : LevelOneProlongationPair P)
  (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
  (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
  (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)

namespace ChartFstSupply

variable {R S₁}


end ChartFstSupply


end Chart

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

end
