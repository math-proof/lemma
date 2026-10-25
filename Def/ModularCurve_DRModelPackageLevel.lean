import Mathlib
import Lemma.ModularCurve.IgusaScheme
import Def.GaloisRep_Flat
import Lemma.ModularCurve.AtkinLehnerPartial
import Lemma.AlgebraicCurve.CurveModel
import Lemma.ModularCurve.GeometricBaseChange
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.ModularCurve.PlaceWidthChar
import Lemma.ModularCurve.CoeffSemilinearAut
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Structure.ModularCurve_DRModelPackageLevel
import Abbrev.ModularCurve_DRModelPackageLevel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]


namespace DRLevel


def sectionFibreOver {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : R q →+* A) (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ q)) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue A).comp ρ) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s.1) (𝟙 _) (by
    rw [Category.assoc, s.2, Category.id_comp, ← Spec.map_comp, CommRingCat.ofHom_comp])

end DRLevel

open DRLevel


namespace DRModelPackageLevel

variable {N₀ q} {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)


def πw : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q) :=
  ⟨𝔛.w.hom ≫ 𝔛.π.1, by rw [Category.assoc, 𝔛.π.2, 𝔛.w_over]⟩

@[simp] theorem πw_val : 𝔛.πw.1 = 𝔛.w.hom ≫ 𝔛.π.1 := rfl

end DRModelPackageLevel

end ModularCurve

end
