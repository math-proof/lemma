import Class.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']

/-- TEMP: real pullbackConstants belongs in Def/. -/
noncomputable def Divisor.pullbackConstants (K' : Type*) (F' : Type*)
    [Field K'] [Field F'] [Algebra K' F'] (D : Divisor K F) : Divisor K' F' := 0

variable (K K' F F') in

class ConstantFieldDegreeFormula : Prop where
  degree_pullbackConstants : ∀ D : Divisor K F,
    Divisor.degree (Divisor.pullbackConstants (K := K) (F := F) K' F' D) = Divisor.degree D

end AlgebraicCurve
