import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
open PicardProjective
open MvPolynomial


namespace PicardProjective

/--
[mvPolynomial_fin_ufd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma mvPolynomial_fin_ufd
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  UniqueFactorizationMonoid (MvPolynomial (Fin n) k) :=
-- proof
  inferInstance

end PicardProjective

namespace PicardProjective

/--
[mvPolynomial_ufd_of_ufd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma mvPolynomial_ufd_of_ufd
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [UniqueFactorizationMonoid R]
  {σ : Type*} :
-- imply
  UniqueFactorizationMonoid (MvPolynomial σ R) :=
-- proof
  inferInstance

end PicardProjective

namespace PicardProjective

/--
[degree_zero_equiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma degree_zero_equiv_one
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p : HomogFraction σ k}
-- given
  (hdeg : p.degree σ k = 0) :
-- imply
  p.PicEquiv σ k (HomogFraction.one σ k) := by
-- proof
  have hdeq : p.ndeg = p.ddeg := by unfold HomogFraction.degree at hdeg; omega
  refine ⟨p.num, p.den, p.ndeg, p.ddeg, p.num_ne, p.den_ne,
    p.nhom, p.dhom, hdeq, ?_⟩
  simp only [HomogFraction.one]
  have : p.num * p.den * 1 = 1 * p.num * p.den := by ring
  rw [this]

end PicardProjective

namespace PicardProjective

/--
[degree_twistingSheafPow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma degree_twistingSheafPow
  {k : Type*}
  [Field k]
  {n : ℕ}
  {d : ℤ} :
-- imply
  (gradedPicardGroup_equiv_int k n) (twistingSheafPow n k d) = d := by
-- proof
  simp only [gradedPicardGroup_equiv_int, AddEquiv.ofBijective,
    GradedPicardGroup.degreeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact twistFraction_degree n k d

end PicardProjective

namespace PicardProjective

/--
[degree_twistingSheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma degree_twistingSheaf
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  (gradedPicardGroup_equiv_int k n) (twistingSheaf n k) = 1 :=
-- proof
  degree_twistingSheafPow k n 1

end PicardProjective

namespace PicardProjective

/--
[picardGroup_generated_by_O1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
lemma picardGroup_generated_by_O1
  {k : Type*}
  [Field k]
  {n : ℕ}
  {L : GradedPicardGroup (Fin (n + 1)) k} :
-- imply
  ∃ d : ℤ, L = twistingSheafPow n k d := by
-- proof
  use (gradedPicardGroup_equiv_int k n) L
  apply (gradedPicardGroup_equiv_int k n).injective
  rw [degree_twistingSheafPow]

end PicardProjective

/--
[homogeneous_degree_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma homogeneous_degree_unique_eq
  [Field k]
  {f : MvPolynomial σ k}
  {d₁ d₂ : ℕ}
-- given
  (hf : f ≠ 0)
  (h0 : f.IsHomogeneous d₁)
  (h1 : f.IsHomogeneous d₂) :
-- imply
  d₁ = d₂ := by
-- proof
  apply PicardProjective.homogeneous_degree_unique hf h0 h1

/--
[isUnit_isHomogeneous_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma isUnit_isHomogeneous_zero_eq
  [Field k]
  {u : MvPolynomial σ k}
-- given
  (hu : IsUnit u) :
-- imply
  u.IsHomogeneous 0 := by
-- proof
  apply PicardProjective.isUnit_isHomogeneous_zero hu

/--
[associated_homogeneous_same_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma associated_homogeneous_same_degree_eq
  [Field k]
  {f g : MvPolynomial σ k}
  {d₁ d₂ : ℕ}
-- given
  (hg : g ≠ 0)
  (hfh : f.IsHomogeneous d₁)
  (hgh : g.IsHomogeneous d₂)
  (h : Associated f g) :
-- imply
  d₁ = d₂ := by
-- proof
  apply PicardProjective.associated_homogeneous_same_degree hg hfh hgh h

/--
[HomogFraction.PicEquiv.rfl'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma rfl'_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p : HomogFraction σ k} :
-- imply
  p.PicEquiv σ k p := by
-- proof
  apply PicardProjective.HomogFraction.PicEquiv.rfl' σ k p

/--
[HomogFraction.PicEquiv.symm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma symm'_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p q : HomogFraction σ k}
-- given
  (h : p.PicEquiv σ k q) :
-- imply
  q.PicEquiv σ k p := by
-- proof
  apply PicardProjective.HomogFraction.PicEquiv.symm' σ k h

/--
[HomogFraction.PicEquiv.trans'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma trans'_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p q r : HomogFraction σ k}
-- given
  (h0 : p.PicEquiv σ k q)
  (h1 : q.PicEquiv σ k r) :
-- imply
  p.PicEquiv σ k r := by
-- proof
  apply PicardProjective.HomogFraction.PicEquiv.trans' σ k h0 h1

/--
[degree_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma degree_compat_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p q : HomogFraction σ k}
-- given
  (h : p.PicEquiv σ k q) :
-- imply
  p.degree σ k = q.degree σ k := by
-- proof
  apply PicardProjective.degree_compat σ k p q h

/--
[mul_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma mul_compat_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p₁ p₂ q₁ q₂ : HomogFraction σ k}
-- given
  (hp : p₁.PicEquiv σ k p₂)
  (hq : q₁.PicEquiv σ k q₂) :
-- imply
  (p₁.mul σ k q₁).PicEquiv σ k (p₂.mul σ k q₂) := by
-- proof
  apply PicardProjective.mul_compat σ k hp hq

/--
[inv_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma inv_compat_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p q : HomogFraction σ k}
-- given
  (h : p.PicEquiv σ k q) :
-- imply
  (p.inv σ k).PicEquiv σ k (q.inv σ k) := by
-- proof
  apply PicardProjective.inv_compat σ k h

/--
[ring_assoc_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma ring_assoc_equiv_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {p q : HomogFraction σ k}
-- given
  (hn : p.num = q.num)
  (hd : p.den = q.den)
  (_ : p.ndeg = q.ndeg)
  (_ : p.ddeg = q.ddeg) :
-- imply
  p.PicEquiv σ k q := by
-- proof
  apply PicardProjective.ring_assoc_equiv σ k p q hn hd _ _

/--
[degreeMap_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma degreeMap_add_eq
  {σ : Type*}
  {k : Type*}
  [Field k]
  {a b : GradedPicardGroup σ k} :
-- imply
  GradedPicardGroup.degreeMap σ k (a + b) = GradedPicardGroup.degreeMap σ k a + GradedPicardGroup.degreeMap σ k b := by
-- proof
  apply PicardProjective.degreeMap_add σ k a b

/--
[twistFraction_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma twistFraction_degree_eq
  {n : ℕ}
  {k : Type*}
  [Field k]
  {d : ℤ} :
-- imply
  (twistFraction n k d).degree (Fin (n + 1)) k = d := by
-- proof
  apply PicardProjective.twistFraction_degree n k d

/--
[degreeHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma degreeHom_surjective_eq
  {n : ℕ}
  {k : Type*}
  [Field k] :
-- imply
  Function.Surjective (GradedPicardGroup.degreeHom (Fin (n + 1)) k) := by
-- proof
  apply PicardProjective.degreeHom_surjective n k

/--
[degreeHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean)
-/
@[path]
private lemma degreeHom_injective_eq
  {σ : Type*}
  {k : Type*}
  [Field k] :
-- imply
  Function.Injective (GradedPicardGroup.degreeHom σ k) := by
-- proof
  apply PicardProjective.degreeHom_injective σ k


-- created on 2026-10-23
