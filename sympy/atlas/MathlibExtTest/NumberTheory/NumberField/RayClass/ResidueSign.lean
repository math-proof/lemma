/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/ResidueSign.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.ResidueSign
import Lemma.Nat.NumberField.RayClass.ResidueSign

@[expose] public noncomputable section

open NumberField
open NumberField.Modulus

namespace ResidueSignTest

variable {K : Type*} [Field K] [NumberField K]

-- Pointwise evaluation of the combined residue-sign map.
example (m : Modulus K) (x : rayElements m) :
    residueSignMap m x = (infiniteSignMap m x, finiteResidueMap m x) :=
  residueSignMap_apply m x

-- Surjectivity on an arbitrary generic target pair.
example (m : Modulus K) (t : ResidueSignTarget m) :
    ∃ x : rayElements m, residueSignMap m x = t :=
  residueSignMap_surjective m t

-- Ray-one membership is finite congruence plus infinite positivity.
example (m : Modulus K) (x : rayElements m) :
    x ∈ rayOneElements m ↔
      CongruentOneAtFinitePart m (x : Kˣ) ∧
        PositiveAtInfinitePart m (x : Kˣ) :=
  mem_rayOneElements_iff m x

-- The combined map is trivial exactly on ray-one elements.
example (m : Modulus K) (x : rayElements m) :
    residueSignMap m x = 1 ↔ IsRayElementOne m (x : Kˣ) :=
  residueSignMap_eq_one_iff m x

-- The quotient equivalence evaluated on a class representative.
example (m : Modulus K) (x : rayElements m) :
    rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x) =
      residueSignMap m x :=
  rayElementsQuotientEquivResidueSign_mk m x

-- Direct generic consumer of the kernel characterization.
example (m : Modulus K) :
    (residueSignMap m).ker = rayOneElements m :=
  residueSignMap_ker m

-- Unit-modulus boundary over `ℚ`: the finite coordinate is one.
example (x : rayElements (1 : Modulus ℚ)) :
    (residueSignMap (1 : Modulus ℚ) x).2 = 1 := by
  rw [residueSignMap_apply, finiteResidueMap_eq_one_iff]
  intro v hv
  exact absurd hv (by
    intro h
    have htop : (⊤ : Ideal (𝓞 ℚ)) ≤ v.asIdeal := by
      simpa [finiteSupported] using h
    exact v.isPrime.ne_top (top_le_iff.mp htop))

end ResidueSignTest
