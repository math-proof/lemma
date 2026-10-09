import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

open Polynomial

/--
[primitiveTriple_of_no_common_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma primitiveTriple_of_no_common_irreducible_eq
  [Field K]
-- given
  {a b c : K[X]}
  (hc : c ≠ 0)
  (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
-- imply
  AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree.PrimitiveTriple a b c :=
-- proof
  AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree.primitiveTriple_of_no_common_irreducible hc h


/--
[projective_first_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma projective_first_natDegree_eq
  [Field K]
-- given
  {u v h : K[X]}
  (hprimitive : AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree.PrimitiveTriple u v h)
  (hh : h ≠ 0)
  {x y : RatFunc K}
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hprod : algebraMap K[X] (RatFunc K) u / algebraMap K[X] (RatFunc K) h = x * y)
  (hsum : algebraMap K[X] (RatFunc K) v / algebraMap K[X] (RatFunc K) h = x + y) :
-- imply
  u.natDegree = x.num.natDegree + y.num.natDegree :=
-- proof
  AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree.projective_first_natDegree
    hprimitive hh hx hy hprod hsum


-- created on 2026-10-09
