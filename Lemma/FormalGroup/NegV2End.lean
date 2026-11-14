-- Instance-notation and End/linearPart material split from
-- Lemma/MvFormalGroup/NegV2.lean so the core module no longer imports
-- Instance.MvFormalGroup_NegV2 (that import cycled with this file).
import Lemma.MvPowerSeries.NegV2
import Lemma.MvPowerSeries.EndRingV2LinearPart
import Instance.MvFormalGroup_NegV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

@[simp]
theorem toPowerSeries_neg' [IsComm G] (φ : Hom F G) :
    (-φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl

@[simp]
theorem toPowerSeries_sub [IsComm G] (φ ψ : Hom F G) :
    (φ - ψ).toPowerSeries = fun i =>
      subst (Sum.elim φ.toPowerSeries (negSeries G ψ.toPowerSeries))
        (G.toPowerSeries i) := rfl

end Hom

namespace End

variable (F : MvFormalGroup g R)

@[simp]
theorem toPowerSeries_neg [IsComm F] (φ : End F) :
    Hom.toPowerSeries (-φ) = negSeries F (Hom.toPowerSeries φ) := rfl

@[simp]
theorem toPowerSeries_sub [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ - ψ) = fun i =>
      subst (Sum.elim (Hom.toPowerSeries φ) (negSeries F (Hom.toPowerSeries ψ)))
        (F.toPowerSeries i) := rfl

theorem toPowerSeries_neg_one [IsComm F] :
    Hom.toPowerSeries (-1 : End F) = invSeries F := by
  rw [toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (1 : End F)) = invSeries F
  rw [toPowerSeries_one]
  rfl

theorem toPowerSeries_intCast_ofNat [IsComm F] (n : ℕ) :
    Hom.toPowerSeries (((n : ℕ) : ℤ) : End F) = F.nthSeries n := by
  rw [Int.cast_natCast]
  exact toPowerSeries_natCast F n

theorem toPowerSeries_intCast_negSucc [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((Int.negSucc n : ℤ) : End F)
      = negSeries F (F.nthSeries (n + 1)) := by
  rw [Int.cast_negSucc, toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (((n + 1 : ℕ) : End F))) = _
  rw [toPowerSeries_natCast]

end End

section InvHom

variable (F : MvFormalGroup g R)

def invHom [IsComm F] : End F := -(1 : End F)

@[simp]
theorem toPowerSeries_invHom [IsComm F] :
    Hom.toPowerSeries (invHom F) = invSeries F :=
  End.toPowerSeries_neg_one F

end InvHom

section LinearPartNeg

variable (F : MvFormalGroup g R)

theorem linearPart_negSeries {k : ℕ} {a : Fin g → MvPowerSeries (Fin k) R}
    (ha : ∀ j, (a j).constantCoeff = 0) :
    linearPart (negSeries F a) = - linearPart a := by
  ext i j
  show coeff (Finsupp.single j 1) (negSeries F a i)
    = (- linearPart a) i j
  rw [coeff_single_negSeries F ha j i, Matrix.neg_apply]
  rfl

theorem coeff_single_invSeries (t i : Fin g) :
    coeff (Finsupp.single t 1) (invSeries F i)
      = - coeff (Finsupp.single t 1) (X i : MvPowerSeries (Fin g) R) :=
  coeff_single_negSeries F (fun l => constantCoeff_X l) t i

theorem linearPart_invSeries : linearPart (invSeries F) = -1 := by
  classical
  ext i j
  show coeff (Finsupp.single j 1) (invSeries F i)
    = (-1 : Matrix (Fin g) (Fin g) R) i j
  rw [coeff_single_invSeries F j i, coeff_index_single_X, Matrix.neg_apply,
    Matrix.one_apply]
  by_cases hij : j = i
  · subst hij
    rfl
  · rw [if_neg hij, if_neg fun hcon => hij hcon.symm, neg_zero]

@[simp]
theorem linearPartHom_neg [IsComm F] (φ : End F) :
    linearPartHom F (-φ) = - linearPartHom F φ :=
  map_neg (linearPartHom F) φ

theorem linearPartHom_neg_one [IsComm F] :
    linearPartHom F (-1 : End F) = -1 := by
  rw [map_neg, map_one]

@[simp]
theorem linearPartHom_intCast [IsComm F] (n : ℤ) :
    linearPartHom F ((n : ℤ) : End F) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [map_intCast, zsmul_eq_mul, mul_one]

end LinearPartNeg

end MvFormalGroup
