import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec20EulerSequence
open QCohProjective TwistSheaf EulerSequence


namespace EulerSequence

/--
[canonical_bundle_eq_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20EulerSequence.lean)
-/
@[path]
lemma canonical_bundle_eq_twist
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  ∀ d : ℤ, Nonempty (GrLinEquiv k n (canonicalBundleGM k n) (serreTwist k n (-(↑n + 1 : ℤ))) d) := by
-- proof
  intro d
  exact ⟨LinearEquiv.refl k _⟩
end EulerSequence



-- created on 2026-10-23
