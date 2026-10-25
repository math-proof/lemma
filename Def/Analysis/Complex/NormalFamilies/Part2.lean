import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
open Set Filter Topology

/-!
# Normal families: Montel's and Vitali's theorems

Proves `Wanted` entries `montel` and `vitali`.
-/


namespace Complex.NormalFamilies

/-- Local uniform boundedness of `F` on `U`: every `x ∈ U` has neighbourhood `V ⊆ U`
and `C ≥ 0` with `‖F n y‖ ≤ C` for all `n` and `y ∈ V`. -/
def IsLocallyUniformlyBoundedOn (U : Set ℂ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ V, ‖F n y‖ ≤ C

end Complex.NormalFamilies
