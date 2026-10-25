import Mathlib
import Def.TateCurve_XMultStructure

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section UnitSpectatorFamily

variable {q : K}

noncomputable def unitSpectator (q : K) (n : ℕ) : K := 1 + q ^ (n + 1)

end UnitSpectatorFamily


section SpectatorUpgrade

variable {q : K}

noncomputable def spectatorRows (s : ℕ → ℕ → Finset ℤ) (a : ℕ → ℕ → ℤ → K) (v : K) :
    ℕ → ℕ → K :=
  fun M k => ∑ j ∈ s M k, a M k j * v ^ j

end SpectatorUpgrade

end TateCurve
