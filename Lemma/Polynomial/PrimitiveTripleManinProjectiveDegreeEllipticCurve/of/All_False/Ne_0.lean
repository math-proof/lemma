import Mathlib
import sympy.Basic
import sympy.polys.agca.elliptic_curve.manin_projective_degree

open Polynomial


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[common_dvd_isUnit_of_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma common_dvd_isUnit_of_isCoprime {p a b : K[X]}
  (hab : IsCoprime a b) (hpa : p ∣ a) (hpb : p ∣ b) : IsUnit p := by
  obtain ⟨a', ha⟩ := hpa
  obtain ⟨b', hb⟩ := hpb
  obtain ⟨u, v, huv⟩ := hab
  refine isUnit_iff_exists_inv.mpr ⟨u * a' + v * b', ?_⟩
  calc
    p * (u * a' + v * b') = u * (p * a') + v * (p * b') := by ring
    _ = 1 := by rw [← ha, ← hb, huv]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[gcd_three_isUnit_of_no_common_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma gcd_three_isUnit_of_no_common_irreducible {a b c : K[X]}
  (hc : c ≠ 0)
  (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
  IsUnit (EuclideanDomain.gcd a (EuclideanDomain.gcd b c)) := by
  by_contra hunit
  have hg0 : EuclideanDomain.gcd a (EuclideanDomain.gcd b c) ≠ 0 := by
    simp only [ne_eq, EuclideanDomain.gcd_eq_zero_iff]
    tauto
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor hunit hg0
  apply h p hp
  · exact hpg.trans (EuclideanDomain.gcd_dvd_left _ _)
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
    (EuclideanDomain.gcd_dvd_left _ _))
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
    (EuclideanDomain.gcd_dvd_right _ _))

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/--
[primitiveTriple_of_no_common_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
lemma primitiveTriple_of_no_common_irreducible
  [Field K]
-- given
  {a b c : K[X]}
  (hc : c ≠ 0)
  (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
-- imply
  EllipticCurve.ManinProjectiveDegree.PrimitiveTriple a b c :=
-- proof
  EllipticCurve.ManinProjectiveDegree.primitiveTriple_of_no_common_irreducible hc h

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[primitiveTriple_linearCombination](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma primitiveTriple_linearCombination {a b c : K[X]}
  (h : PrimitiveTriple a b c) :
  ∃ u v w : K[X], u * a + v * b + w * c = 1 :=
h

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[dvd_of_primitiveTriple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma dvd_of_primitiveTriple {a b c p x : K[X]}
  (h : PrimitiveTriple a b c)
  (ha : p ∣ x * a) (hb : p ∣ x * b) (hc : p ∣ x * c) : p ∣ x := by
  obtain ⟨u, v, w, huv⟩ := primitiveTriple_linearCombination h
  have hdvd : p ∣ u * (x * a) + v * (x * b) + w * (x * c) :=
    ((ha.mul_left u).add (hb.mul_left v)).add (hc.mul_left w)
  have heq : u * (x * a) + v * (x * b) + w * (x * c) = x := by
    calc
      u * (x * a) + v * (x * b) + w * (x * c) =
        x * (u * a + v * b + w * c) := by ring
      _ = x := by rw [huv, mul_one]
  rwa [heq] at hdvd

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[primitive_numeratorTriple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma primitive_numeratorTriple {a b c d : K[X]}
  (hab : IsCoprime a b) (hcd : IsCoprime c d)
  (hb : b ≠ 0) (hd : d ≠ 0) :
  PrimitiveTriple (a * c) (a * d + b * c) (b * d) := by
  apply primitiveTriple_of_no_common_irreducible (mul_ne_zero hb hd)
  intro p hp hpac hpsum hpbd
  have hprime := hp.prime
  obtain hpa | hpc := hprime.dvd_mul.mp hpac
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
    · have hpad : p ∣ a * d := hpa.mul_right d
      have hpbc : p ∣ b * c := by
        have hdvd := hpsum.sub hpad
        have heq : (a * d + b * c) - a * d = b * c := by ring
        rwa [heq] at hdvd
      obtain hpb | hpc := hprime.dvd_mul.mp hpbc
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · have hpbc : p ∣ b * c := hpb.mul_right c
      have hpad : p ∣ a * d := by
        have hdvd := hpsum.sub hpbc
        have heq : (a * d + b * c) - b * c = a * d := by ring
        rwa [heq] at hdvd
      obtain hpa | hpd := hprime.dvd_mul.mp hpad
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[ratFunc_num_denom_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma ratFunc_num_denom_mul (x y : RatFunc K) :
  algebraMap K[X] (RatFunc K) (x.num * y.num) /
    algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x * y := by
  rw [map_mul, map_mul, ← div_mul_div_comm]
  rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

variable {K : Type u} [Field K]
/--
[ratFunc_num_denom_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
private lemma ratFunc_num_denom_add (x y : RatFunc K) :
  algebraMap K[X] (RatFunc K)
    (x.num * y.denom + x.denom * y.num) /
    algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x + y := by
  rw [map_add, map_mul, map_mul, map_mul]
  calc
    _ = algebraMap K[X] (RatFunc K) x.num /
      algebraMap K[X] (RatFunc K) x.denom +
      algebraMap K[X] (RatFunc K) y.num /
        algebraMap K[X] (RatFunc K) y.denom := by
      field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x),
        RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero y)]
    _ = x + y := by
      rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/--
[projective_first_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean)
-/
@[path]
lemma projective_first_natDegree
  [Field K]
-- given
  {u v h : K[X]}
  (hprimitive : EllipticCurve.ManinProjectiveDegree.PrimitiveTriple u v h)
  (hh : h ≠ 0)
  {x y : RatFunc K}
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hprod : algebraMap K[X] (RatFunc K) u / algebraMap K[X] (RatFunc K) h = x * y)
  (hsum : algebraMap K[X] (RatFunc K) v / algebraMap K[X] (RatFunc K) h = x + y) :
-- imply
  u.natDegree = x.num.natDegree + y.num.natDegree :=
-- proof
  EllipticCurve.ManinProjectiveDegree.projective_first_natDegree
    hprimitive hh hx hy hprod hsum


-- created on 2026-10-09
-- updated on 2026-10-23
