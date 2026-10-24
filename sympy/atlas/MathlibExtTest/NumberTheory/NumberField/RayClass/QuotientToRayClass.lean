/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.QuotientToRayClass
import Lemma.Nat.NumberField.RayClass.QuotientToRayClass

@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace N406QuotientToRayClassTest

variable {K : Type*} [Field K] [NumberField K]

-- Representative evaluation of the ray-element class map.
example (m : Modulus K) (x : Modulus.rayElements m) :
    Modulus.rayElementClassMap m x =
      Modulus.rayClassMap m (Modulus.principalRayIdealMap m x) :=
  Modulus.rayElementClassMap_apply m x

-- Ray-one triviality: ray-one elements lie in the class-map kernel.
example (m : Modulus K) (x : Modulus.rayElements m)
    (h : x ∈ Modulus.rayOneElements m) :
    Modulus.rayElementClassMap m x = 1 := by
  have := Modulus.rayOneElements_le_rayElementClassMap_ker m h
  rwa [MonoidHom.mem_ker] at this

-- Quotient representative rule.
example (m : Modulus K) (x : Modulus.rayElements m) :
    Modulus.rayQuotientToRayClassGroup m (QuotientGroup.mk x) =
      Modulus.rayElementClassMap m x :=
  Modulus.rayQuotientToRayClassGroup_mk m x

-- Integral-unit/principal-ideal join: embedded units map to one.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    Modulus.principalRayIdealMap m (Modulus.integralUnitsToRayElements m u) =
      1 :=
  Modulus.principalRayIdealMap_integralUnitsToRayElements m u

-- Raw kernel: kernel equals the range of the integral-unit quotient map.
example (m : Modulus K) :
    (Modulus.rayQuotientToRayClassGroup m).ker =
      MonoidHom.range (Modulus.integralUnitsToRayQuotient m) :=
  Modulus.rayQuotientToRayClassGroup_ker m

-- Transported kernel: kernel equals the range of the residue-sign unit map.
example (m : Modulus K) :
    (Modulus.residueSignToRayClassGroup m).ker =
      MonoidHom.range (Modulus.integralUnitsToResidueSign m) :=
  Modulus.residueSignToRayClassGroup_ker m

-- Raw MulExact at the quotient.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralUnitsToRayQuotient m)
      (Modulus.rayQuotientToRayClassGroup m) :=
  Modulus.integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup m

-- Transported MulExact at the residue-sign target.
example (m : Modulus K) :
    Function.MulExact (Modulus.integralUnitsToResidueSign m)
      (Modulus.residueSignToRayClassGroup m) :=
  Modulus.integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup m

-- Transport square: precomposing with the residue-sign map recovers the class map.
example (m : Modulus K) :
    (Modulus.residueSignToRayClassGroup m).comp (Modulus.residueSignMap m) =
      Modulus.rayElementClassMap m :=
  Modulus.residueSignToRayClassGroup_comp_residueSignMap m

-- Transported evaluation on a residue-sign value.
example (m : Modulus K) (x : Modulus.rayElements m) :
    Modulus.residueSignToRayClassGroup m (Modulus.residueSignMap m x) =
      Modulus.rayElementClassMap m x :=
  Modulus.residueSignToRayClassGroup_residueSignMap m x

-- Identity boundary: the quotient map sends `1` to `1`.
example (m : Modulus K) :
    Modulus.rayQuotientToRayClassGroup m 1 = 1 :=
  map_one _

-- Pointwise forward exactness: unit classes map to one.
example (m : Modulus K) (u : (𝓞 K)ˣ) :
    Modulus.rayQuotientToRayClassGroup m
      (Modulus.integralUnitsToRayQuotient m u) = 1 := by
  have h := Modulus.integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup m
  rw [MonoidHom.mulExact_iff] at h
  have hmem : Modulus.integralUnitsToRayQuotient m u ∈
      MonoidHom.range (Modulus.integralUnitsToRayQuotient m) :=
    ⟨u, rfl⟩
  rw [← h] at hmem
  rwa [MonoidHom.mem_ker] at hmem

-- Pointwise reverse exactness: kernel classes come from integral units.
example (m : Modulus K) (q : Modulus.rayElements m ⧸ Modulus.rayOneElements m)
    (h : Modulus.rayQuotientToRayClassGroup m q = 1) :
    ∃ u : (𝓞 K)ˣ,
      Modulus.integralUnitsToRayQuotient m u = q := by
  have hmem : q ∈ (Modulus.rayQuotientToRayClassGroup m).ker := h
  rw [Modulus.rayQuotientToRayClassGroup_ker] at hmem
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨u, hu⟩

end N406QuotientToRayClassTest
