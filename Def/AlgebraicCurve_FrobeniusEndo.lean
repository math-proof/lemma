module

public import Def.AlgebraicCurve_Correspondence
public import Mathlib.Algebra.CharP.Reduced
public import Structure.AlgebraicCurve_FrobeniusEndo

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Package

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (ℓ : ℕ)


variable {ℓ : ℕ} {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo

def frobNorm (h : IsFrobeniusEndo ℓ φ) (f : F) : F :=
  (h.pow_mem_range f).choose

end IsFrobeniusEndo

end Package

end AlgebraicCurve

end

end
