-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfKummerProp17.lean: instance decls only.
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.Rank
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfGmRepresentable
import Lemma.AlgebraicGeometry.FppfKummerProp17

namespace ModularCurve

namespace AdmissibleInvariants

variable {p : ℕ}

instance : Add (AdmissibleInvariants p) :=
  ⟨fun I J => ⟨I.δ + J.δ, I.α + J.α, I.h0 + J.h0, I.h1 + J.h1⟩⟩

instance : Zero (AdmissibleInvariants p) := ⟨⟨0, 0, 0, 0⟩⟩

end AdmissibleInvariants


end ModularCurve

set_option autoImplicit false

universe w' w v u

open CategoryTheory Abelian Limits


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

end
