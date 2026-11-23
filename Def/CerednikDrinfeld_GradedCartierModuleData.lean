import Mathlib
import Def.CerednikDrinfeld_SpecialFormalModule
import Structure.CerednikDrinfeld_GradedCartierModuleData

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld


namespace GradedCartierModuleData


variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

def homothety (D : GradedCartierModuleData p B j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

def HasStructureConstants (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : D.M,
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[N] h

def IsBaseChangeAlong {B' : Type} [CommRing B'] (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' (φ.comp j))
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))

end GradedCartierModuleData

end CerednikDrinfeld

end
