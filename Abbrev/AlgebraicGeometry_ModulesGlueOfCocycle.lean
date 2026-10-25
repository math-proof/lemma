import Mathlib
import Lemma.AlgebraicGeometry.ModulesSectionsTensor

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}

namespace GlueOfCocycle

noncomputable abbrev rO {A B : X.Opens} (h : B ≤ A) : Γ(X, A) →+* Γ(X, B) :=
  (X.presheaf.map (homOfLE h).op).hom

end GlueOfCocycle

open GlueOfCocycle


namespace UnitCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U)

end UnitCocycle

namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)

end GlueOfCocycle

variable {U : ι → X.Opens}

end AlgebraicGeometry.Scheme.Modules
