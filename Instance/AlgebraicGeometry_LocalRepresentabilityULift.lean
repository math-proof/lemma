-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_LocalRepresentabilityULift.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.LocalRepresentabilityULift

set_option autoImplicit false

universe w v u

open CategoryTheory Category Limits Opposite


namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

instance : IsOpenImmersion (toGlued hf i) :=
  inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

set_option backward.isDefEq.respectTransparency false in
instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (uliftYonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ uliftYoneda.{w}.map (toGlued hf i)) ≫
      (uliftYonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

instance : Sheaf.IsLocallyInjective (uliftYonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ ⟨α⟩ ⟨β⟩ h
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨α⟩ = (uliftYonedaGluedToSheaf hf).hom.app _ ⟨β⟩ := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩

    change V ⟶ X i at a
    change V ⟶ X j at b
    change a ≫ toGlued hf i = γ ≫ α at fac₁
    change b ≫ toGlued hf j = γ ≫ β at fac₂
    change ULift.up (γ ≫ α) = ULift.up (γ ≫ β)
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ α⟩ =
        (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ β⟩ := by
      dsimp at h; simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    apply congrArg ULift.up
    apply comp_toGlued_eq
    simp at h
    apply uliftYonedaEquiv.{w}.injective
    have ha := uliftYonedaEquiv_naturality (X := op (X i)) (f i) a.op
    have hb := uliftYonedaEquiv_naturality (X := op (X j)) (f j) b.op
    exact ha.symm.trans (h.trans hb)

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

instance : IsIso (uliftYonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (uliftYonedaGluedToSheaf hf)]
  constructor <;> infer_instance

end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
