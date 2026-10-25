-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FGSubalgebra.lean: instance decls only.
import Mathlib

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]


namespace FGSubalgebra

instance : Nonempty (FGSubalgebra R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance : IsDirected (FGSubalgebra R A) (· ≤ ·) :=
  ⟨fun A₀ A₁ ↦ ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩,
    (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1), (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1)⟩⟩

instance : IsFiltered (FGSubalgebra R A) := inferInstance

instance (A₀ : Subalgebra R A) : IsDirected {A₁ : FGSubalgebra R A // A₀ ≤ A₁.1} (· ≤ ·) :=
  ⟨fun A₁ A₂ ↦ ⟨⟨⟨A₁.1.1 ⊔ A₂.1.1, A₁.1.2.sup A₂.1.2⟩, A₁.2.trans (le_sup_left : A₁.1.1 ≤ _)⟩,
    (le_sup_left : A₁.1.1 ≤ A₁.1.1 ⊔ A₂.1.1), (le_sup_right : A₂.1.1 ≤ A₁.1.1 ⊔ A₂.1.1)⟩⟩

instance (A₀ : FGSubalgebra R A) : Nonempty {A₁ : FGSubalgebra R A // A₀.1 ≤ A₁.1} := ⟨⟨A₀, le_rfl⟩⟩


instance : IsCofiltered (FGSubalgebra R A)ᵒᵖ := inferInstance


instance (i : (FGSubalgebra R A)ᵒᵖ) : IsAffine ((specDiagram R A).obj i) :=
  inferInstanceAs (IsAffine (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : CompactSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (CompactSpace (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

instance {i j : (FGSubalgebra R A)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiagram R A).map f) :=
  isAffineHom_of_isAffine _

end FGSubalgebra

end AlgebraicGeometry
