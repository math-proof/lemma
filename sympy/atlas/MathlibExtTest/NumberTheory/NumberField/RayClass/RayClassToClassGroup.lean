/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.RayClassToClassGroup
import Lemma.Nat.NumberField.RayClass.RayClassToClassGroup

@[expose] public noncomputable section

open scoped nonZeroDivisors
open NumberField

namespace N406RayClassToClassGroupTest

variable {K : Type*} [Field K] [NumberField K]

-- Representative evaluation of the coprime ideal-class map.
example (m : Modulus K) (I : Modulus.coprimeFractionalIdeals m) :
    Modulus.coprimeIdealClassMap m I =
      ClassGroup.mk K ((Modulus.coprimeFractionalIdeals m).subtype I) :=
  Modulus.coprimeIdealClassMap_apply m I

-- Ray-group triviality: ray-group elements lie in the class-map kernel.
example (m : Modulus K) (y : Modulus.coprimeFractionalIdeals m)
    (h : y ∈ Modulus.rayGroup m) :
    Modulus.coprimeIdealClassMap m y = 1 := by
  have := Modulus.rayGroup_le_coprimeIdealClassMap_ker m h
  rwa [MonoidHom.mem_ker] at this

-- Projection representative rule.
example (m : Modulus K) (I : Modulus.coprimeFractionalIdeals m) :
    Modulus.rayClassToClassGroup m (Modulus.rayClassMap m I) =
      Modulus.coprimeIdealClassMap m I :=
  Modulus.rayClassToClassGroup_rayClassMap m I

-- Projection composition rule.
example (m : Modulus K) :
    (Modulus.rayClassToClassGroup m).comp (Modulus.rayClassMap m) =
      Modulus.coprimeIdealClassMap m :=
  Modulus.rayClassToClassGroup_comp_rayClassMap m

-- Raw kernel: kernel equals the range of the quotient map.
example (m : Modulus K) :
    (Modulus.rayClassToClassGroup m).ker =
      MonoidHom.range (Modulus.rayQuotientToRayClassGroup m) :=
  Modulus.rayClassToClassGroup_ker m

-- Raw MulExact at the ray class group.
example (m : Modulus K) :
    Function.MulExact (Modulus.rayQuotientToRayClassGroup m)
      (Modulus.rayClassToClassGroup m) :=
  Modulus.rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup m

-- Transported MulExact at the ray class group.
example (m : Modulus K) :
    Function.MulExact (Modulus.residueSignToRayClassGroup m)
      (Modulus.rayClassToClassGroup m) :=
  Modulus.residueSignToRayClassGroup_mulExact_rayClassToClassGroup m

-- Pointwise forward exactness: quotient classes map to one.
example (m : Modulus K)
    (q : Modulus.rayElements m ⧸ Modulus.rayOneElements m)
    (hq : ∃ x : Modulus.rayElements m, QuotientGroup.mk x = q) :
    Modulus.rayClassToClassGroup m
        (Modulus.rayQuotientToRayClassGroup m q) = 1 := by
  obtain ⟨x, rfl⟩ := hq
  have h := Modulus.rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup m
  rw [MonoidHom.mulExact_iff] at h
  have hmem : Modulus.rayQuotientToRayClassGroup m (QuotientGroup.mk x) ∈
      MonoidHom.range (Modulus.rayQuotientToRayClassGroup m) :=
    ⟨_, rfl⟩
  rw [← h] at hmem
  rwa [MonoidHom.mem_ker] at hmem

-- Pointwise reverse exactness: kernel classes come from the quotient map.
example (m : Modulus K) (c : Modulus.RayClassGroup m)
    (h : Modulus.rayClassToClassGroup m c = 1) :
    ∃ q, Modulus.rayQuotientToRayClassGroup m q = c := by
  have hmem : c ∈ (Modulus.rayClassToClassGroup m).ker := h
  rw [Modulus.rayClassToClassGroup_ker] at hmem
  obtain ⟨q, hu⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨q, hu⟩

-- Transported reverse exactness: kernel classes come from residue signs.
example (m : Modulus K) (c : Modulus.RayClassGroup m)
    (h : Modulus.rayClassToClassGroup m c = 1) :
    ∃ s, Modulus.residueSignToRayClassGroup m s = c := by
  have hmul := Modulus.residueSignToRayClassGroup_mulExact_rayClassToClassGroup m
  rw [MonoidHom.mulExact_iff] at hmul
  have hmem : c ∈ (Modulus.rayClassToClassGroup m).ker := h
  rw [hmul] at hmem
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨s, hs⟩

-- Quotient composition on generators.
example (m : Modulus K) (x : Modulus.rayElements m) :
    Modulus.rayClassToClassGroup m
        (Modulus.rayQuotientToRayClassGroup m (QuotientGroup.mk x)) =
      Modulus.coprimeIdealClassMap m (Modulus.principalRayIdealMap m x) :=
  Modulus.rayClassToClassGroup_rayQuotientToRayClassGroup m x

-- Residue-sign composition on generators.
example (m : Modulus K) (x : Modulus.rayElements m) :
    Modulus.rayClassToClassGroup m
        (Modulus.residueSignToRayClassGroup m (Modulus.residueSignMap m x)) =
      Modulus.coprimeIdealClassMap m (Modulus.principalRayIdealMap m x) :=
  Modulus.rayClassToClassGroup_residueSignToRayClassGroup m x

-- Identity boundary: the projection sends `1` to `1`.
example (m : Modulus K) :
    Modulus.rayClassToClassGroup m 1 = 1 :=
  map_one _

end N406RayClassToClassGroupTest
