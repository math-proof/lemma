-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule.lean: instance decls only.
import Mathlib
import Def.AlgebraicGeometry_OModulePresheafHom
import Instance.AlgebraicGeometry_ProjTwistDatum
import Lemma.AlgebraicGeometry.OModulePresheafFamilyFramesGradedModule

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry


namespace OModulePresheaf

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}


section Ambient

variable (G : ℕ → OModulePresheaf q)

instance FamilyFrames.addCommGroup : AddCommGroup (FamilyFrames ι G) :=
  inferInstanceAs (AddCommGroup (ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)))

instance FamilyFrames.module : Module A (FamilyFrames ι G) :=
  inferInstanceAs (Module A (ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)))

variable {ι G}

variable (ι G)

variable {ι G}

variable (ι G)

variable {ι G}

end Ambient

section Family

variable [IsAffineHom ι] (G : ℕ → OModulePresheaf q) {s : ℕ}

variable {ι G θ}

variable (ι G θ)

variable {ι G θ}

variable (ι G θ)

instance familyFramesGradedModule.moduleBase (hθ : YComm G θ) : Module A (familyFramesGradedModule ι G θ hθ).M :=
  FamilyFrames.module ι G

variable {ι G θ}

end Family

end OModulePresheaf

end AlgebraicGeometry

end
