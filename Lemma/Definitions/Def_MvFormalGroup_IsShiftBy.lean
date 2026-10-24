import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_FirstOrderDeformation

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup.Deformation

open IsLocalRing

def IsShiftBy {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) {d : ℕ} (F : MvFormalGroup d B)
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' : Deformation (F.map (algebraMap B B₁)) B) : Prop :=
  ∃ (n : ℕ) (v : Fin n → V) (z : Fin n → ↥(firstOrderCocycles (F.map (residue B))))
    (zl : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
    (∀ i l, MvPowerSeries.map (residue B) (zl i l) = (z i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l) ∧
    (∀ ξ : Module.Dual (ResidueField B) V, w ξ = ∑ i, ξ (v i) • Submodule.Quotient.mk (z i)) ∧
    (∀ l, G'.F.toPowerSeries l = G.F.toPowerSeries l + ∑ i, ι (v i) • zl i l)

end MvFormalGroup.Deformation

end
