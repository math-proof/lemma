import Lemma.ModularCurve.JZeroSemistableSpecialization
import Structure.ModularCurve_PlaceSpecialization
import Def.ModularCurve_GlueData

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)


theorem fstDiv_zero : P.fstDiv 0 = 0 := by
  ext W
  simp [fstDiv, Finsupp.filter_apply]

theorem sndDiv_zero : P.sndDiv 0 = 0 := by
  ext W
  simp [sndDiv, Finsupp.filter_apply]

theorem glueData_zero
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    P.glueData S 0 = 0 := by
  simp only [glueData, fstDiv_zero, sndDiv_zero, Finsupp.mapDomain_zero]
  rfl

theorem isGoodDiv_zero : P.IsGoodDiv 0 := fun W hW => absurd hW (by simp)

theorem isGoodClass_zero
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    P.IsGoodClass S 0 := by
  refine ⟨0, P.isGoodDiv_zero, ?_, rfl⟩
  rw [ZeroMemClass.coe_zero, glueData_zero]
  exact zero_mem _

example (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (h : ∀ W, ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W)
    (sp : ↥(inertiaInvariants A (N * q)) →+ GluedPic0 k (modularFunctionFieldC k N) S) :
    P.IsGluedSpecialization S sp := by
  intro D hH x hgood hx
  have hD : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = 0 := by
    ext W
    by_contra hW
    rcases hgood W (Finsupp.mem_support_iff.mpr hW) with h1 | h2
    · exact (h W).1 h1
    · exact (h W).2 h2
  have hD0 : D = 0 := Subtype.ext hD
  subst hD0
  have hx0 : (x : GluingData k (modularFunctionFieldC k N) S) = 0 := by
    rw [hx, ZeroMemClass.coe_zero, glueData_zero]
  have hx0' : x = 0 := Subtype.ext hx0
  subst hx0'
  have hmk : (⟨Pic0.mk (0 : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar (N * q))))), hH⟩ : ↥(inertiaInvariants A (N * q))) = 0 :=
    Subtype.ext rfl
  rw [hmk, map_zero, map_zero]

end PlaceSpecialization

end ModularCurve

end
