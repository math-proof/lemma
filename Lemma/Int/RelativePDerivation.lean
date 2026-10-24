import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.RelativePDerivation
open MetaMathlibExt
open RelativePDerivation


namespace MetaMathlibExt.RelativePDerivation

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
lemma ext
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d₁ d₂ : RelativePDerivation p u}
-- given
  (h : ∀ x, (d₁ : A → B) x = (d₂ : A → B) x) :
-- imply
  d₁ = d₂ := by
-- proof
  cases d₁ with
  | mk f₁ h1₁ h2₁ h3₁ =>
    cases d₂ with
    | mk f₂ h1₂ h2₂ h3₂ =>
      simp only [mk.injEq]
      funext x
      exact h x

end MetaMathlibExt.RelativePDerivation

namespace MetaMathlibExt.RelativePDerivation

/--
[coe_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
lemma coe_mk
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x : A} :
-- imply
  (d : A → B) x = d.toFun x :=
-- proof
  rfl

end MetaMathlibExt.RelativePDerivation

namespace MetaMathlibExt.RelativePDerivation

/--
[map_one_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
lemma map_one_eq_zero
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u} :
-- imply
  (d : A → B) 1 = 0 :=
-- proof
  d.map_one

end MetaMathlibExt.RelativePDerivation

namespace MetaMathlibExt.RelativePDerivation

/--
[map_add_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
lemma map_add_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x y : A} :
-- imply
  (d : A → B) (x + y) =
      (d : A → B) x + (d : A → B) y + pDerivationCorrection p (u x) (u y) :=
-- proof
  d.map_add x y

end MetaMathlibExt.RelativePDerivation

namespace MetaMathlibExt.RelativePDerivation

/--
[map_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RelativePDerivation.lean)
-/
@[path]
lemma map_mul_eq
  [CommRing A] [CommRing B]
  {p : ℕ} [Fact p.Prime]
  {u : A →+* B}
  {d : RelativePDerivation p u}
  {x y : A} :
-- imply
  (d : A → B) (x * y) =
      (u x) ^ p * (d : A → B) y + (u y) ^ p * (d : A → B) x +
        (p : B) * (d : A → B) x * (d : A → B) y :=
-- proof
  d.map_mul x y

end MetaMathlibExt.RelativePDerivation


-- created on 2026-10-20
-- updated on 2026-10-23
