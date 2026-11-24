module
public import Def.ModularCurve_FinitePlaceLift
public import Def.AlgebraicCurve_RatFuncPlaces
public import Theorem.Valuation.RatFuncPlaceInfty
public import Def.AlgebraicCurve_SemistableCharts


public section

namespace AlgebraicCurve.GaussReduction

open Polynomial

variable {K : Type*} [Field K] (A : ValuationSubring K)

noncomputable def gaussVal (P : K[X]) : A.ValueGroup :=
  P.support.sup fun i => A.valuation (P.coeff i)

noncomputable def gaussValuationPoly : Valuation K[X] A.ValueGroup where
  toFun := gaussVal A
  map_zero' := gaussVal_zero A
  map_one' := gaussVal_one A
  map_mul' := gaussVal_mul A
  map_add_le_max' := gaussVal_add_le A

noncomputable def gaussValuation : Valuation (RatFunc K) A.ValueGroup :=
  (gaussValuationPoly A).extendToLocalization (nonZeroDivisors_le_primeCompl A) (RatFunc K)

noncomputable def gaussIntegers : ValuationSubring (RatFunc K) :=
  (gaussValuation A).valuationSubring

noncomputable def constToGauss : ↥A →+* ↥(gaussIntegers A) where
  toFun c := ⟨algebraMap K (RatFunc K) (c : K), by
    rw [mem_gaussIntegers_iff, gaussValuation_algebraMap_const]
    exact A.valuation_le_one c⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

noncomputable def xGauss : ↥(gaussIntegers A) :=
  ⟨algebraMap K[X] (RatFunc K) Polynomial.X, by
    rw [mem_gaussIntegers_iff, gaussValuation_algebraMap_poly, gaussVal_X]⟩

noncomputable def polyToGauss : Polynomial ↥A →+* ↥(gaussIntegers A) :=
  Polynomial.eval₂RingHom (constToGauss A) (xGauss A)

noncomputable def residueConstHom :
    IsLocalRing.ResidueField ↥A →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  IsLocalRing.ResidueField.map (constToGauss A)

noncomputable def psiPoly :
    Polynomial (IsLocalRing.ResidueField ↥A) →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  Polynomial.eval₂RingHom (residueConstHom A)
    (IsLocalRing.residue ↥(gaussIntegers A) (xGauss A))

noncomputable def psiRatFunc :
    RatFunc (IsLocalRing.ResidueField ↥A) →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  IsFractionRing.lift (psiPoly_injective A)

noncomputable def psiEquiv :
    RatFunc (IsLocalRing.ResidueField ↥A) ≃+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  RingEquiv.ofBijective (psiRatFunc A) ⟨(psiRatFunc A).injective, psiRatFunc_surjective A⟩

noncomputable def gaussResidue :
    ↥(gaussIntegers A) →+* RatFunc (IsLocalRing.ResidueField ↥A) :=
  ((psiEquiv A).symm : IsLocalRing.ResidueField ↥(gaussIntegers A) →+* _).comp
    (IsLocalRing.residue ↥(gaussIntegers A))

section PlaceMap

open RationalFunctionField
open scoped Classical

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
end PlaceMap


end AlgebraicCurve.GaussReduction


namespace AlgebraicCurve

open IsLocalRing

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

noncomputable def ofConstantReductionNodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    ComponentChart A F Fbar where
  integers := R.integers
  residue := R.residue
  dom := {P | R.placeMap P ∉ nodes}
  nodes := nodes
  placeMap := R.placeMap
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  placeMap_not_mem_nodes := fun _ h => h
  pointwise := fun P hPdom hP f hf hfib =>
    hR P hP f hf (fun w hw => hfib w (show R.placeMap w ∉ nodes by rw [hw]; exact hPdom) hw)
  mapDomain_placeMap := fun f hf D hDdom hDoff Q hQ => by
end ComponentChart

namespace StandardAnnulus

open Polynomial RationalFunctionField GaussReduction


section Admissible

variable {K : Type*} [Field K] (A : ValuationSubring K)

def Admissible (π : A) (a : K) : Prop :=
  A.valuation (π : K) < A.valuation a ∧ A.valuation a < 1

variable {A}

end Admissible

section Poly

variable {K : Type*} [Field K] (A : ValuationSubring K)

noncomputable def innerCount (p : K[X]) : ℕ :=
  Multiset.card (p.roots.filter fun r => A.valuation r < 1)

variable {A}

end Poly


section TheAnnulus

variable {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)

noncomputable def standardAnnulus (π : A) (hπ : π ∈ maximalIdeal A) : Annulus A (RatFunc K) where
  dom := {P | ∃ a : K, Admissible A π a ∧ P = placeOfPoint K a}
  param := RatFunc.X
  modulus := π
  modulus_mem := hπ
  mem_dom := by
    rintro P ⟨a, ha, rfl⟩
    refine ⟨isRational_placeOfPoint a, X_mem_placeOfPoint a, ?_, ?_, ?_⟩
    · rw [evalAt_placeOfPoint_X]
      exact ⟨ha.mem, ha.mem_maximalIdeal⟩
    · rw [evalAt_placeOfPoint_X]
      exact ha.ne_zero
    · rw [evalAt_placeOfPoint_X]
      exact ha.exists_eq_mul
  existsUnique_evalAt_eq := by
    intro c hc hc0 hm
    have hadm : Admissible A π c := admissible_of π c hc hc0 hm
    refine ⟨placeOfPoint K c, ⟨⟨c, hadm, rfl⟩, evalAt_placeOfPoint_X (c : K)⟩, ?_⟩
    rintro P ⟨⟨a, ha, rfl⟩, hPa⟩
    rw [evalAt_placeOfPoint_X] at hPa
    rw [hPa]
  ord_param_sub := by
    rintro P ⟨a, ha, rfl⟩
    rw [evalAt_placeOfPoint_X, ord_placeOfPoint_X_sub]
  unit_principle := by
    intro f hf0 hordf
    obtain ⟨c, hcg, hres⟩ := exists_smul_gaussResidue_ne_zero A f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres
      have h0 : (⟨(0 : K) • f, hcg⟩ : ↥(gaussIntegers A)) = 0 := Subtype.ext (zero_smul K f)
      rw [h0, map_zero]
    have hordg : ∀ a : K, Admissible A π a → (placeOfPoint K a).ord (c • f) = 0 := by
      intro a ha
      rw [Algebra.smul_def, (placeOfPoint K a).ord_mul ((_root_.map_ne_zero _).mpr hc0) hf0,
        ord_algebraMap_eq_zero _ hc0, hordf (placeOfPoint K a) ⟨a, ha, rfl⟩, add_zero]
    refine ⟨(placeOfPoint (ResidueField ↥A) 0).ord (gaussResidue A ⟨c • f, hcg⟩), c⁻¹, inv_ne_zero hc0, ?_⟩
    rintro P ⟨a, ha, rfl⟩
    have hcore := exists_isUnit_evalAt_mul_zpow A π ⟨c • f, hcg⟩ hres hordg ha
    have hPl := isRational_placeOfPoint (K := K) a
    have hfmem : f ∈ (placeOfPoint K a).toValuationSubring :=
      mem_of_ord_nonneg_gen _ hf0 (by rw [hordf (placeOfPoint K a) ⟨a, ha, rfl⟩])
    have hsmul : (placeOfPoint K a).evalAt ((⟨c • f, hcg⟩ : ↥(gaussIntegers A)) : RatFunc K)
        = (placeOfPoint K a).evalAt f * c⁻¹⁻¹ := by
      rw [inv_inv, show (((⟨c • f, hcg⟩ : ↥(gaussIntegers A)) : RatFunc K)) = c • f from rfl, Algebra.smul_def,
        evalAt_mul_of_mem _ hPl ((placeOfPoint K a).algebraMap_mem' c) hfmem, evalAt_algebraMap_const _ hPl, mul_comm]
    rw [hsmul] at hcore
    exact hcore

end TheAnnulus

section Degenerate

variable {K : Type*} [Field K]

attribute [local instance] ConstantReduction.ofTopAlgebra in

noncomputable def _root_.AlgebraicCurve.ComponentChart.ofConstantReductionNodesSelf (L : Type*) [Field L]
    (nodes : Finset (Place (ResidueField ↥(⊤ : ValuationSubring L)) L)) :
    ComponentChart (⊤ : ValuationSubring L) L L :=
  ComponentChart.ofConstantReductionNodes (ConstantReduction.ofTop L L)
    (ConstantReduction.isPointwise_ofTop L L) nodes
    (fun _ _ => ⟨0, fun P => (ConstantReduction.isEmpty_place_self L).elim P⟩)

end Degenerate

end StandardAnnulus

end AlgebraicCurve
