/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/MetricSpace/LipschitzParametrizable.lean -/


import sympy.atlas.Topology.MetricSpace.LipschitzParametrizable
import Lemma.Set.MetricSpace.LipschitzParametrizable

/-!
# Tests for N384 (Definition 19.4): Lipschitz parametrizable sets
-/

-- The origin lies in the dimension-0 cube.
example : (0 : Fin 0 → ℝ) ∈ unitCube 0 :=
  unitCube_zero_mem 0

-- Empty set in dimension 0.
example : IsLipschitzParametrizable 0 (∅ : Set ℝ) :=
  isLipschitzParametrizable_empty 0

-- Singleton in dimension 0.
example (x : ℝ) : IsLipschitzParametrizable 0 ({x} : Set ℝ) :=
  isLipschitzParametrizable_singleton 0 x

-- Singleton in positive dimension.
example (x : ℝ) : IsLipschitzParametrizable 1 ({x} : Set ℝ) :=
  isLipschitzParametrizable_singleton 1 x

-- Finset coercion in positive dimension.
example (s : Finset ℝ) : IsLipschitzParametrizable 2 (↑s : Set ℝ) :=
  Finset.isLipschitzParametrizable_coe 2 s

-- Finite sets in positive dimension.
example {B : Set ℝ} (hB : B.Finite) : IsLipschitzParametrizable 3 B :=
  hB.isLipschitzParametrizable 3

-- The definition unfolded: a singleton is one Lipschitz range over the cube.
example (x : ℝ) :
    ∃ (n : ℕ) (f : Fin n → (↥(unitCube 1) → ℝ)),
      (∀ i, ∃ K : NNReal, LipschitzWith K (f i)) ∧
        ({x} : Set ℝ) = ⋃ i, Set.range (f i) :=
  isLipschitzParametrizable_singleton 1 x

namespace LipschitzParametrizableImageTest

-- Generic API use: pushing any parametrizable set forward along a Lipschitz map.
example {B : Set ℝ} (hB : IsLipschitzParametrizable 1 B) {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : IsLipschitzParametrizable 1 (f '' B) :=
  hB.image_lipschitzWith hf

-- Concrete example: the identity map preserves parametrizability.
example {B : Set ℝ} (hB : IsLipschitzParametrizable 2 B) :
    IsLipschitzParametrizable 2 (id '' B) :=
  hB.image_lipschitzWith LipschitzWith.id

-- Concrete example: the identity map on a singleton source, end to end.
example (x : ℝ) : IsLipschitzParametrizable 1 (id '' ({x} : Set ℝ)) := by
  have h : IsLipschitzParametrizable 1 ({x} : Set ℝ) :=
    isLipschitzParametrizable_singleton 1 x
  simpa using h.image_lipschitzWith LipschitzWith.id

end LipschitzParametrizableImageTest
