import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannFormRR
open RiemannFormRR
open scoped TensorProduct


namespace RiemannFormRR

/--
[SatisfiesRiemannRoch.rr_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannFormRR.lean)
-/
@[path]
lemma SatisfiesRiemannRoch.rr_formula
  [Field k]
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A]
  {I : Ideal A}
-- given
  (h : SatisfiesRiemannRoch k A)
  (hI : I ≠ ⊥) :
-- imply
  divisorEulerChar k A I = (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 - (RiemannRochGeneral.arithmeticGenus k A : ℤ) :=
-- proof
  h I hI

end RiemannFormRR

namespace RiemannFormRR

/--
[lD_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannFormRR.lean)
-/
@[path]
lemma lD_top
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A] :
-- imply
  lD k A ⊤ = Module.finrank k A :=
-- proof
  LinearEquiv.finrank_eq (homTopEquiv k A A)

end RiemannFormRR

namespace RiemannFormRR

/--
[lKD_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannFormRR.lean)
-/
@[path]
lemma lKD_top
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A] :
-- imply
  lKD k A ⊤ = Module.finrank k (Ω[A⁄k]) :=
-- proof
  LinearEquiv.finrank_eq (homTopEquiv k A (Ω[A⁄k]))

end RiemannFormRR

namespace RiemannFormRR

/--
[riemann_roch_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannFormRR.lean)
-/
@[path]
lemma riemann_roch_field
  {k : Type*}
  [Field k]
  {I : Ideal k}
-- given
  (hI : I ≠ ⊥) :
-- imply
  @divisorEulerChar k _ k _ _ _ (Algebra.id k) I = (@RiemannRochGeneral.lineBundleDegree k _ k _ _ (Algebra.id k) I : ℤ) + 1 - (@RiemannRochGeneral.arithmeticGenus k _ k _ _ _ (Algebra.id k) inferInstance : ℤ) := by
-- proof
  have hItop : I = ⊤ := by
    obtain h | h := I.eq_bot_or_top
    · exact absurd h hI
    · exact h
  subst hItop
  unfold divisorEulerChar lD lKD RiemannRochGeneral.lineBundleDegree RiemannRochGeneral.arithmeticGenus
  haveI hss : Subsingleton (Ω[k⁄k]) :=
    KaehlerDifferential.subsingleton_of_surjective k k (fun x => ⟨x, rfl⟩)
  have hg : Module.finrank k (Ω[k⁄k]) = 0 := Module.finrank_zero_of_subsingleton
  haveI : Subsingleton (k ⧸ (⊤ : Ideal k)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hdeg : Module.finrank k (k ⧸ (⊤ : Ideal k)) = 0 := Module.finrank_zero_of_subsingleton
  have hlD : Module.finrank k (↥(⊤ : Ideal k) →ₗ[k] k) = 1 := by
    rw [LinearEquiv.finrank_eq (homTopEquiv k k k), Module.finrank_self]
  haveI : Subsingleton (↥(⊤ : Ideal k) →ₗ[k] Ω[k⁄k]) := by
    constructor; intro f g; ext x; exact Subsingleton.elim _ _
  have hlKD : Module.finrank k (↥(⊤ : Ideal k) →ₗ[k] Ω[k⁄k]) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hlD, hlKD, hdeg, hg]
  norm_num

end RiemannFormRR


-- created on 2026-10-23
