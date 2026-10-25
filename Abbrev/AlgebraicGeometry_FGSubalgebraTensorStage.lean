import Mathlib
import Instance.AlgebraicGeometry_FGSubalgebra

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.FGSubalgebra

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]
  (Γ : Type u) [CommRing Γ] [Algebra k Γ]

abbrev tensorStage (D : FGSubalgebra k A) : Type u := Γ ⊗[k] ↥D.1

noncomputable abbrev tensorStageMap (D D' : FGSubalgebra k A) (h : D ≤ D') :
    tensorStage k A Γ D →ₐ[Γ] tensorStage k A Γ D' :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) (Subalgebra.inclusion (show D.1 ≤ D'.1 from h))

noncomputable abbrev tensorStageToColimit (D : FGSubalgebra k A) : tensorStage k A Γ D →ₐ[Γ] Γ ⊗[k] A :=
  Algebra.TensorProduct.map (AlgHom.id Γ Γ) D.1.val


end AlgebraicGeometry.FGSubalgebra
