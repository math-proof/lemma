import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
open nonZeroDivisors RiemannRochGeneral
open scoped TensorProduct


namespace RiemannRochGeneral

/--
[kaehler_polynomial_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma kaehler_polynomial_rank
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank (Polynomial k) (Ω[Polynomial k⁄k]) = 1 := by
-- proof
  rw [LinearEquiv.finrank_eq (KaehlerDifferential.polynomialEquiv k),
    Module.finrank_self]

end RiemannRochGeneral

namespace RiemannRochGeneral

/--
[idealDegree_bot_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma idealDegree_bot_field
  {k : Type*}
  [Field k] :
-- imply
  @idealDegree k _ k _ _ (Algebra.id k) ⊥ Ideal.bot_isMaximal = 1 := by
-- proof
  unfold idealDegree
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k k).toLinearEquiv,
    Module.finrank_self]

end RiemannRochGeneral

namespace RiemannRochGeneral

/--
[lineBundleDegree_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma lineBundleDegree_top
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A] :
-- imply
  lineBundleDegree k A ⊤ = 0 := by
-- proof
  unfold lineBundleDegree
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

end RiemannRochGeneral

namespace RiemannRochGeneral

/--
[lineBundleDegree_eq_idealDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma lineBundleDegree_eq_idealDegree
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  {I : Ideal A}
  [I.IsMaximal] :
-- imply
  lineBundleDegree k A I = idealDegree k A I :=
-- proof
  rfl

end RiemannRochGeneral

namespace RiemannRochGeneral

/--
[riemann_roch_rank_one_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma riemann_roch_rank_one_identity
  {d : ℤ}
  {g : ℕ} :
-- imply
  d + (1 : ℤ) * (1 - (g : ℤ)) = d + 1 - g := by
-- proof
ring

end RiemannRochGeneral

namespace RiemannRochGeneral

/--
[lineBundleDegree_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeneral.lean)
-/
@[path]
lemma lineBundleDegree_bot
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A] :
-- imply
  lineBundleDegree k A ⊥ = Module.finrank k A := by
-- proof
  unfold lineBundleDegree
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k A).toLinearEquiv]

end RiemannRochGeneral


-- created on 2026-10-23
