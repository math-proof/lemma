import Mathlib
import Structure.ModularCurve_JZeroNeronAtPDataSameIdeal

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataOrdCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPDataSameIdeal N q hqN A hA where

  inertia_sub_mem_fin : ∀ (m : ℕ), m ≠ 0 → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion (N * q) m, σ • x - x ∈ fin m


end ModularCurve

end
