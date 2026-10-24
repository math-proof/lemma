/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/InfiniteSign.lean -/

import sympy.atlas.NumberTheory.NumberField.RayClass.InfiniteSign
import Lemma.Nat.NumberField.RayClass.InfiniteSign

@[expose] public noncomputable section

open NumberField
open NumberField.Modulus

variable {K : Type*} [Field K] [NumberField K]

-- Multiplicativity of the sign at a real place.
example (w : RealPlace K) (x y : Kˣ) :
    signAtRealPlace w (x * y) = signAtRealPlace w x * signAtRealPlace w y :=
  map_mul _ _ _

-- Exact pointwise evaluation of the joint sign map.
example (m : Modulus K) (x : rayElements m) (w : m.infinitePart) :
    infiniteSignMap m x w = signAtRealPlace (w : RealPlace K) (x : Kˣ) :=
  infiniteSignMap_apply m x w

-- Kernel/positivity equivalence.
example (m : Modulus K) (x : rayElements m) :
    x ∈ positiveRayElements m ↔ PositiveAtInfinitePart m (x : Kˣ) :=
  mem_positiveRayElements_iff m x

-- The identity ray element is positive at infinity.
example (m : Modulus K) : (1 : rayElements m) ∈ positiveRayElements m := by
  rw [mem_positiveRayElements_iff]
  change PositiveAtInfinitePart m 1
  exact positiveAtInfinitePart_one m
