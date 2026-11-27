module

public import Mathlib
public import Def.ModularForm_HeckeOperator

public section

namespace ModularForm

axiom heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (heckeU k p f) = heckeU k p f

end ModularForm
