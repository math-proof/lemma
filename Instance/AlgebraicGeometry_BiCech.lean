-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_BiCech.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Instance.AlgebraicGeometry_DoubleComplex
import Lemma.AlgebraicGeometry.BiCech

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry


namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔄 : Z.OrderedOpenFamily)

instance instFintypeIdx (p : ℕ) : Fintype (𝔄.Idx p) := Subtype.fintype _

instance instDecidableEqIdx (p : ℕ) : DecidableEq (𝔄.Idx p) := Classical.decEq _

end Scheme.OrderedOpenFamily


end AlgebraicGeometry

end
