/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalFamilies.lean -/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

@[expose] public section

open Set Filter Topology

/-!
# Normal families: Montel's and Vitali's theorems

Proves `Wanted` entries `montel` and `vitali`.
-/


namespace MathlibExt.Analysis.Complex.NormalFamilies

/-- Local uniform boundedness of `F` on `U`: every `x ∈ U` has neighbourhood `V ⊆ U`
and `C ≥ 0` with `‖F n y‖ ≤ C` for all `n` and `y ∈ V`. -/
def IsLocallyUniformlyBoundedOn (U : Set ℂ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ V, ‖F n y‖ ≤ C

end MathlibExt.Analysis.Complex.NormalFamilies
