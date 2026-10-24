import Mathlib
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule

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

def homothety (D : GradedCartierModuleData p B j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

@[simp] theorem homothety_apply (D : GradedCartierModuleData p B j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x := rfl

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

def IsHomogeneousVBasis (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) : Prop :=
  (∀ i : Fin 2, γ i ∈ D.piece i) ∧
    ∀ x : D.M, ∃! cy : (Fin 2 → B) × D.M,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) + D.verschiebung cy.2

def IsVAdicallyComplete (D : GradedCartierModuleData p B j) : Prop :=
  ∀ x : ℕ → D.M, ∃! s : D.M, ∀ N : ℕ, ∃ t : D.M,
    s = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (x m)) + (⇑D.verschiebung)^[N] t

def IsSpecialCartierModule (D : GradedCartierModuleData p B j) : Prop :=
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ) ∧ D.IsVAdicallyComplete

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

theorem varpi_smul (D : GradedCartierModuleData p B j) (w : WittVector p B) (x : D.M) :
    D.varpi (w • x) = w • D.varpi x := map_smul _ _ _

theorem verschiebung_frobenius (D : GradedCartierModuleData p B j) (x : D.M) :
    D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]

theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p B j) (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) := (D.frobenius_verschiebung x).symm

theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩

theorem IsHomogeneousVBasis.verschiebung_injective {D : GradedCartierModuleData p B j}
    {γ : Fin 2 → D.M} (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung := by
  intro y y' hyy
  have key := h.2 (D.verschiebung y)
  obtain ⟨cy, hcy, huniq⟩ := key
  have h1 : ((fun _ => (0 : B)), y) = cy := huniq ((fun _ => (0 : B)), y) (by simp)
  have h2 : ((fun _ => (0 : B)), y') = cy := huniq ((fun _ => (0 : B)), y') (by simp [hyy])
  have := h1.trans h2.symm
  simpa using congrArg Prod.snd this

end GradedCartierModuleData

end CerednikDrinfeld

end
