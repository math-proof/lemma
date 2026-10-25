import Lemma.AlgebraicCurve.DivisorClassGroup
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Class.AlgebraicCurve_IsCurveOver

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

variable {K F}

theorem hasPrincipalDivisors [h : IsCurveOver K F] : HasPrincipalDivisors K F :=
  h.toHasPrincipalDivisors

theorem finite_residueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  IsCurveOver.finiteResidue v

theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=
  h.kaehler_free_rank_one.2

end IsCurveOver

namespace Place

variable {K F}

theorem deg_eq_one_of_isAlgClosed_of_finite [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace IsCurveOver

variable {K F}

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.deg = 1 :=
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  v.deg_eq_one_of_isAlgClosed_of_finite

theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :
    ∀ w : Place K F, w.deg = 1 :=
  deg_eq_one_of_isAlgClosed

end IsCurveOver

end AlgebraicCurve
