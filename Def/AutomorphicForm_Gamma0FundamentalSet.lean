module

public import Mathlib
public import Theorem.UpperHalfPlane.FundamentalDomainVolume
public import Theorem.UpperHalfPlane.SiegelSetCover
public import Instance.AutomorphicForm_Gamma0FundamentalSet

@[expose] public section

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise

namespace FLT.Gamma0FundamentalSet

def gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟


def truncatedGammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) (y : ℝ) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • truncatedFundamentalDomain y

end FLT.Gamma0FundamentalSet
