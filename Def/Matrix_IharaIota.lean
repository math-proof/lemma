module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Inclusion

def ι₀ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N :=
  Subgroup.inclusion (Gamma0_mul_le N q)

end Inclusion

section Conjugation

def iota1Mat (q : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 * (q : ℤ); g 1 0 / (q : ℤ), g 1 1]

def iota1SL (N q : ℕ) (γ : Gamma0 (N * q)) : SL(2, ℤ) :=
  ⟨iota1Mat q (γ : SL(2, ℤ)), by
    rw [det_iota1Mat (q_dvd_entry N q γ)]
    exact (γ : SL(2, ℤ)).det_coe⟩

def ι₁ (N q : ℕ) : Gamma0 (N * q) →* Gamma0 N where
  toFun γ := ⟨iota1SL N q γ, iota1SL_mem N q γ⟩
  map_one' := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_one q
  map_mul' γ δ := Subtype.ext <| Subtype.ext <| by
    simpa using iota1Mat_mul (q_dvd_entry N q γ) (q_dvd_entry N q δ)

end Conjugation

end Ihara

end
