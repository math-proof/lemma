module

public import Mathlib
public import Theorem.MvPowerSeries.SpecialFormalModule
public import Structure.CerednikDrinfeld_GradedCartierModuleData

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld


namespace GradedCartierModuleData


variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}


@[simp] public theorem homothety_apply (D : GradedCartierModuleData p B j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x := rfl


public theorem verschiebung_frobenius (D : GradedCartierModuleData p B j) (x : D.M) :
    D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]


public theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p B j) (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) := (D.frobenius_verschiebung x).symm


public theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩


public theorem IsHomogeneousVBasis.verschiebung_injective {D : GradedCartierModuleData p B j}
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
