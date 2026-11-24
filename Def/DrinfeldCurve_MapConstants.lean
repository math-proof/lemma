module
public import Def.DrinfeldCurve_FunctionField
public import Def.AlgebraicCurve_Correspondence
public import Instance.DrinfeldCurve_MapConstants
set_option autoImplicit false


public section

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

section Square

variable (q : ℕ) (k k' : Type) [Field k] [Field k'] [Algebra k k']

namespace CoordRing

def mapConstants : CoordRing q k →+* CoordRing q k' :=
  Ideal.Quotient.lift (drinfeldIdeal q k) ((mk q k').toRingHom.comp (MvPolynomial.map (algebraMap k k')))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      have hmem : MvPolynomial.map (algebraMap k k') (b * (drinfeldPoly q k - 1)) ∈ drinfeldIdeal q k' := by
        rw [map_mul, map_sub, map_one, map_drinfeldPoly, drinfeldIdeal]
        exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
      show mk q k' (MvPolynomial.map (algebraMap k k') (b * (drinfeldPoly q k - 1))) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

private def retract (r : k' →ₗ[k] k) (f : MvPolynomial (Fin 2) k') : MvPolynomial (Fin 2) k :=
  ∑ m ∈ f.support, monomial m (r (coeff m f))

end CoordRing

def functionFieldMapConstants [IsDomain (CoordRing q k')] :
    drinfeldFunctionField q k →+* drinfeldFunctionField q k' :=
  IsFractionRing.map (CoordRing.mapConstants_injective q k k')

@[reducible] def constantsAlgebraCoordRing : Algebra k (CoordRing q k') :=
  ((algebraMap k' (CoordRing q k')).comp (algebraMap k k')).toAlgebra

@[reducible] def constantsAlgebraFunctionField : Algebra k (drinfeldFunctionField q k') :=
  letI := constantsAlgebraCoordRing q k k'
  inferInstanceAs (Algebra k (FractionRing (CoordRing q k')))

@[reducible] def functionFieldConstantsAlgebra [IsDomain (CoordRing q k')] :
    Algebra (drinfeldFunctionField q k) (drinfeldFunctionField q k') :=
  (functionFieldMapConstants q k k').toAlgebra

section Equivariance

variable [Fact q.Prime] [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) k']
  [IsScalarTower (GaloisField q 2) k k']

end Equivariance

end Square

end DrinfeldCurve

end
