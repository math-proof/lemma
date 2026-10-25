-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechCup
import Lemma.AlgebraicGeometry.OrderedAffineCoverCochainPullback
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechOrdered
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechOrderedChains

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

instance instDecidableOSub {n k : ℕ} (u : K.OIdx n) (t : K.OIdx k) : Decidable (K.OSub u t) := by
  classical
  exact inferInstance

end Scheme.OrderedAffineCover


end AlgebraicGeometry

end
