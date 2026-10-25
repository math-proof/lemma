import Class.AlgebraicCurve_ConstantFieldPullback
import Def.ModularCurve_DegeneracyVp

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Equivariance

open scoped Pointwise

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra F F']
  {σ : F ≃ₐ[K] F} {σ' : F' ≃ₐ[K'] F'}


end Equivariance

section ClassGroup

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F'] [ConstantFieldDegreeFormula K K' F F']

variable (K K' F F') in

def Pic0.degZeroBaseChangeHom :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((Divisor.pullbackConstants K' F').domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackConstants_mem_degZero D.2)


def Pic0.baseChange : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (degZeroBaseChangeHom K K' F F') (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.pullbackConstants_mem_principal hD)

@[simp]
theorem Pic0.baseChange_mk (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.baseChange K K' F F' (Pic0.mk D) =
      Pic0.mk ⟨Divisor.pullbackConstants K' F' (D : Divisor K F), Divisor.pullbackConstants_mem_degZero D.2⟩ :=
  rfl


end ClassGroup

end AlgebraicCurve

namespace ModularCurve

section Intertwining

variable (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J']
  {G G' : Type} [Monoid G] [Monoid G'] [DistribMulAction G J] [DistribMulAction G' J']


end Intertwining

end ModularCurve

end
