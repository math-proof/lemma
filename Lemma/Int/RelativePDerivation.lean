import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.RelativePDerivation
open MetaMathlibExt
open RelativePDerivation


/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
private lemma ext_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d₁ d₂ : RelativePDerivation p u}
-- given
  (h : ∀ x, (d₁ : A → B) x = (d₂ : A → B) x) :
-- imply
  d₁ = d₂ := by
-- proof
  apply MetaMathlibExt.RelativePDerivation.ext h

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
private lemma coe_mk_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x : A} :
-- imply
  (d : A → B) x = d.toFun x := by
-- proof
  apply MetaMathlibExt.RelativePDerivation.coe_mk d x

/--
[map_one_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
private lemma map_one_eq_zero_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u} :
-- imply
  (d : A → B) 1 = 0 := by
-- proof
  apply MetaMathlibExt.RelativePDerivation.map_one_eq_zero d

/--
[map_add_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
private lemma map_add_eq_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x y : A} :
-- imply
  (d : A → B) (x + y) =
      (d : A → B) x + (d : A → B) y + pDerivationCorrection p (u x) (u y) := by
-- proof
  apply MetaMathlibExt.RelativePDerivation.map_add_eq d x y

/--
[map_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
private lemma map_mul_eq_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x y : A} :
-- imply
  (d : A → B) (x * y) =
      (u x) ^ p * (d : A → B) y + (u y) ^ p * (d : A → B) x +
        (p : B) * (d : A → B) x * (d : A → B) y := by
-- proof
  apply MetaMathlibExt.RelativePDerivation.map_mul_eq d x y


-- created on 2026-10-20
