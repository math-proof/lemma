import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.GaloisField
import Instance.DrinfeldCurve_CoordRing

set_option autoImplicit false

universe u

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

variable (q : ℕ) (k : Type u) [Field k]

def drinfeldPoly : MvPolynomial (Fin 2) k := X 0 * X 1 ^ q - X 0 ^ q * X 1

def drinfeldIdeal : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {drinfeldPoly q k - 1}

def CoordRing : Type u := MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k

def mk : MvPolynomial (Fin 2) k →ₐ[k] CoordRing q k := Ideal.Quotient.mkₐ k (drinfeldIdeal q k)

def x : CoordRing q k := mk q k (X 0)

def y : CoordRing q k := mk q k (X 1)

def scalePoly (c : k) : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun i => C c * X i

section Actions

variable [Fact q.Prime] [Algebra (GaloisField q 2) k]

def ofZMod : ZMod q →+* k :=
  (algebraMap (GaloisField q 2) k).comp (algebraMap (ZMod q) (GaloisField q 2))

def substPoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun j => ∑ i, C (ofZMod q k (g i j)) * X i

private def slEnd (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k) ((mk q k).comp (substPoly q k (g : Matrix (Fin 2) (Fin 2) (ZMod q))))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, map_mul, map_sub, map_one, substPoly_drinfeldPoly,
        Matrix.SpecialLinearGroup.det_coe, map_one, C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private def slEndHom : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := slEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [slEnd_mk, Matrix.SpecialLinearGroup.coe_one, substPoly_one]
  map_mul' g h := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [slEnd_mk, Matrix.SpecialLinearGroup.coe_mul, substPoly_mul]

def slAction : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (slEndHom q k).toHomUnits

def scalarOf (ζ : (GaloisField q 2)ˣ) : k := algebraMap (GaloisField q 2) k ζ

private def muEnd (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k) ((mk q k).comp (scalePoly k (scalarOf q k ζ)))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, map_mul, map_sub, map_one, scalePoly_drinfeldPoly, scalarOf_pow_of_mem q k ζ.2,
        C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private def muEndHom : rootsOfUnity (q + 1) (GaloisField q 2) →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := muEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [muEnd_mk, scalarOf_one, scalePoly_one]
  map_mul' ζ η := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [muEnd_mk, scalarOf_mul, scalePoly_mul]

def muAction : rootsOfUnity (q + 1) (GaloisField q 2) →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (muEndHom q k).toHomUnits

def hChar : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ →* (GaloisField q 2)ˣ :=
  ((Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom).comp
      (Matrix.GeneralLinearGroup.det.comp (MonoidHom.fst _ _))) *
    ((powMonoidHom (q + 1)).comp (MonoidHom.snd _ _))

def hSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) := (hChar q).ker

private def hEnd (p : hSubgroup q) : CoordRing q k →ₐ[k] CoordRing q k :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q k)
    ((mk q k).comp ((scalePoly k (scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) ×
      (GaloisField q 2)ˣ).2)).comp (substPoly q k ((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) ×
      (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)))))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [AlgHom.comp_apply, AlgHom.comp_apply, map_mul, map_sub, map_one, map_mul, map_sub, map_one,
        scalePoly_substPoly_drinfeldPoly, hFactor q k p.2, C_1, one_mul]
      exact mk_mul_drinfeldPoly_sub_one q k _)

private def hEndHom : hSubgroup q →* (CoordRing q k →ₐ[k] CoordRing q k) where
  toFun := hEnd q k
  map_one' := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [hEnd_mk, scalarOf_one, scalePoly_one, substPoly_one]
  map_mul' p₁ p₂ := by
    apply algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.mul_apply, hEnd_mk]
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, Units.val_mul, scalarOf_mul, substPoly_X, scalePoly_X,
      map_mul, map_add, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply, Fin.sum_univ_two]
    ring

def hAction : hSubgroup q →* (CoordRing q k ≃ₐ[k] CoordRing q k) :=
  (AlgEquiv.algHomUnitsEquiv k (CoordRing q k)).toMonoidHom.comp (hEndHom q k).toHomUnits

end Actions

end DrinfeldCurve

end
