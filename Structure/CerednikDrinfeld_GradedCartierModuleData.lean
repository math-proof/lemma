import Mathlib
import Structure.CerednikDrinfeld_SpecialFormalModule

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

structure GradedCartierModuleData (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B]
    (j : Zp2 p →+* B) : Type 1 where

  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module (WittVector p B) M]

  frobenius : M →+ M

  verschiebung : M →+ M

  varpi : M →ₗ[WittVector p B] M

  piece : Fin 2 → Submodule (WittVector p B) M

  frobenius_smul : ∀ (w : WittVector p B) (x : M),
    frobenius (w • x) = WittVector.frobenius w • frobenius x

  smul_verschiebung : ∀ (w : WittVector p B) (x : M),
    w • verschiebung x = verschiebung (WittVector.frobenius w • x)

  verschiebung_smul_frobenius : ∀ (w : WittVector p B) (x : M),
    verschiebung (w • frobenius x) = WittVector.verschiebung w • x

  frobenius_verschiebung : ∀ x : M, frobenius (verschiebung x) = (p : ℕ) • x

  varpi_verschiebung : ∀ x : M, varpi (verschiebung x) = verschiebung (varpi x)

  varpi_frobenius : ∀ x : M, varpi (frobenius x) = frobenius (varpi x)

  varpi_varpi : ∀ x : M, varpi (varpi x) = (p : ℕ) • x

  isCompl_piece : IsCompl (piece 0) (piece 1)

  verschiebung_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → verschiebung x ∈ piece (i + 1)

  frobenius_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → frobenius x ∈ piece (i + 1)

  varpi_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → varpi x ∈ piece (i + 1)

namespace GradedCartierModuleData

attribute [instance] GradedCartierModuleData.addCommGroup GradedCartierModuleData.module

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}


end GradedCartierModuleData

end CerednikDrinfeld

end
