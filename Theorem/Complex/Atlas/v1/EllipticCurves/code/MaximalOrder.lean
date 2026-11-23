module

public import Mathlib

public section

open NumberField


namespace MaximalOrder

/--
[ringOfIntegers_isOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/MaximalOrder.lean)
-/
public theorem ringOfIntegers_isOrder
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Module.Free ℤ (𝓞 K) ∧ Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
-- proof
  ⟨inferInstance, RingOfIntegers.rank K⟩

end MaximalOrder

namespace MaximalOrder

/--
[ringOfIntegers_isMaximalOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/MaximalOrder.lean)
-/
public theorem ringOfIntegers_isMaximalOrder
  {K : Type*}
  [Field K]
  [NumberField K]
  {O : Subalgebra ℤ K}
  [Module.Finite ℤ O] :
-- imply
  O ≤ integralClosure ℤ K := by
-- proof
  intro x hx
  exact (IsIntegral.of_finite ℤ (⟨x, hx⟩ : O)).algebraMap

end MaximalOrder

namespace MaximalOrder

/--
[ringOfIntegers_unique_maximalOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/MaximalOrder.lean)
-/
public theorem ringOfIntegers_unique_maximalOrder
  {K : Type*}
  [Field K]
  [NumberField K]
  {O : Subalgebra ℤ K}
  [Module.Finite ℤ O]
-- given
  (hmax : ∀ (O' : Subalgebra ℤ K), [Module.Finite ℤ O'] → O ≤ O' → O' ≤ O) :
-- imply
  O = integralClosure ℤ K := by
-- proof
  apply le_antisymm
  · exact ringOfIntegers_isMaximalOrder
  · have : Module.Finite ℤ ↥(integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact hmax (integralClosure ℤ K) ringOfIntegers_isMaximalOrder

end MaximalOrder


-- created on 2026-10-23
-- updated on 2026-11-23
