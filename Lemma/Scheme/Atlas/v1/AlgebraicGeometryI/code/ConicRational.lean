import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ConicRational
open ConicRational


namespace ConicRational

/--
[adjoinRoot_inv_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean)
-/
@[path]
lemma adjoinRoot_inv_relation
  {R : Type*}
  [CommRing R]
  {r : R} :
-- imply
  AdjoinRoot.of (invertPoly R r) r * AdjoinRoot.root (invertPoly R r) = 1 :=
-- proof
  AdjoinRoot.root_isInv r

end ConicRational

namespace ConicRational

/--
[hyperbola_xy_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean)
-/
@[path]
lemma hyperbola_xy_eq_one
  {k : Type*}
  [CommRing k] :
-- imply
  AdjoinRoot.of (hyperbolaPoly k) Polynomial.X * AdjoinRoot.root (hyperbolaPoly k) = 1 :=
-- proof
  adjoinRoot_inv_relation (Polynomial k) Polynomial.X

end ConicRational

namespace ConicRational

/--
[genus_conic_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean)
-/
@[path]
lemma genus_conic_eq_zero
-- imply
  genusDeg 2 = 0 := by
-- proof
rfl

end ConicRational

namespace ConicRational

/--
[conic_genus_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean)
-/
@[path]
lemma conic_genus_bridge
-- imply
  genusDeg 2 = RiemannRoch.genus 2 := by
-- proof
  unfold genusDeg RiemannRoch.genus
  rfl

end ConicRational

/--
[powers_X_le_nonZeroDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean)
-/
@[path]
private lemma powers_X_le_nonZeroDivisors_eq
  {k : Type*}
  [Field k] :
-- imply
  Submonoid.powers (Polynomial.X : Polynomial k) ≤ nonZeroDivisors (Polynomial k) := by
-- proof
  apply ConicRational.powers_X_le_nonZeroDivisors k


-- created on 2026-10-23
