import Mathlib
import Instance.GaloisRep_ComplexConjugation
import Def.GaloisRep_ComplexConjugation

set_option autoImplicit false


@[simp] lemma complexConjAlgEquiv_apply (z : ℂ) : complexConjAlgEquiv z = starRingEnd ℂ z := rfl

lemma complexConjAlgEquiv_mul_self : complexConjAlgEquiv * complexConjAlgEquiv = 1 :=
  AlgEquiv.ext fun z => Complex.conj_conj z


theorem complexEmbedding_complexConjugation (x : AlgebraicClosure ℚ) :
    complexEmbedding (complexConjugation x) = starRingEnd ℂ (complexEmbedding x) :=
  AlgEquiv.restrictNormal_commutes complexConjAlgEquiv (AlgebraicClosure ℚ) x

theorem complexConjugation_mul_self : complexConjugation * complexConjugation = 1 := by
  rw [complexConjugation, ← map_mul, complexConjAlgEquiv_mul_self, map_one]

theorem complexConjugation_sq : complexConjugation ^ 2 = 1 := by
  rw [sq]; exact complexConjugation_mul_self

theorem complexConjugation_inv : complexConjugation⁻¹ = complexConjugation :=
  inv_eq_of_mul_eq_one_right complexConjugation_mul_self

namespace ExtCitation


@[simp] lemma archimedeanLoc_archimedeanGen :
    archimedeanLoc archimedeanGen = complexConjugation := rfl

end ExtCitation
