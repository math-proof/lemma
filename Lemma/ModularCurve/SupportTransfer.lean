import Mathlib
import Lemma.CuspForm.HeckeAlgebra
import Lemma.ModularCurve.MazurPrincipleCore
import Def.FLTPrelim_Modularity
import Def.ModularCurve_SupportTransfer

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ExitIdeal

variable (N : ℕ) [NeZero N] (W : WeierstrassCurve ℤ) (p : ℕ)


theorem natCast_mem_exitIdeal : ((p : ℕ) : CuspForm.heckeAlgebra N 2 {n : ℕ | n ∣ N}) ∈ exitIdeal N W p :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem exitGen_mem_exitIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hgood : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p) :
    exitGen N W ℓ hℓ hℓN ∈ exitIdeal N W p :=
  Ideal.subset_span (Set.mem_insert_of_mem _ ⟨ℓ, hℓ, hℓN, hgood, hℓp, rfl⟩)

end ExitIdeal

end ModularCurve

end
