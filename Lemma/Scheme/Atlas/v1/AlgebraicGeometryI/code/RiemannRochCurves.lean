import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
open nonZeroDivisors RiemannRochCurves
open scoped TensorProduct


namespace RiemannRochCurves

/--
[additive_hom_determined_by_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma additive_hom_determined_by_generators
  {f : ℤ × ℤ →+ ℤ} :
-- imply
  ∀ p : ℤ × ℤ, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
-- proof
  intro ⟨r, d⟩
  show f (r, d) = r * f (1, 0) + d * f (0, 1)
  have h1 : (r, d) = (r, 0) + (0, d) := by ext <;> simp
  rw [h1, map_add]
  congr 1
  · have : (r, (0 : ℤ)) = r • (1, 0) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]
  · have : ((0 : ℤ), d) = d • (0, 1) := by ext <;> simp
    rw [this, map_zsmul, smul_eq_mul]

end RiemannRochCurves

namespace RiemannRochCurves

/--
[additive_homs_eq_of_generators_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma additive_homs_eq_of_generators_eq
  {f g : ℤ × ℤ →+ ℤ}
-- given
  (h_OX : f (1, 0) = g (1, 0))
  (h_Ox : f (0, 1) = g (0, 1)) :
-- imply
  f = g := by
-- proof
  ext ⟨r, d⟩
  rw [additive_hom_determined_by_generators f,
    additive_hom_determined_by_generators g, h_OX, h_Ox]

end RiemannRochCurves

namespace RiemannRochCurves

/--
[rrHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma rrHom_apply
  {g : ℤ}
  {r d : ℤ} :
-- imply
  rrHom g (r, d) = d - r * (g - 1) :=
-- proof
  rfl

end RiemannRochCurves

namespace RiemannRochCurves

/--
[finrank_additive_ses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma finrank_additive_ses
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V]
  {W : Submodule k V} :
-- imply
  (Module.finrank k V : ℤ) = (Module.finrank k W : ℤ) + (Module.finrank k (V ⧸ W) : ℤ) := by
-- proof
  have h := Submodule.finrank_quotient_add_finrank W
  omega

end RiemannRochCurves

namespace RiemannRochCurves

/--
[riemann_roch_curves_thm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma riemann_roch_curves_thm
  {g : ℤ}
  {χ : ℤ × ℤ →+ ℤ}
-- given
  (hχ_struct : χ (1, 0) = 1 - g)
  (hχ_sky : χ (0, 1) = 1) :
-- imply
  ∀ r d : ℤ, χ (r, d) = d - r * (g - 1) := by
-- proof
  intro r d
  have heq : χ = rrHom g :=
    additive_homs_eq_of_generators_eq χ (rrHom g)
      (by rw [hχ_struct, rr_value_structure_sheaf])
      (by rw [hχ_sky, rr_value_skyscraper])
  calc χ (r, d) = (rrHom g) (r, d) := by rw [heq]
    _ = d - r * (g - 1) := rrHom_apply g r d

end RiemannRochCurves

namespace RiemannRochCurves

/--
[rr_genus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma rr_genus_zero
  {χ : ℤ × ℤ →+ ℤ}
-- given
  (hχ_struct : χ (1, 0) = 1)
  (hχ_sky : χ (0, 1) = 1) :
-- imply
  ∀ r d : ℤ, χ (r, d) = d + r := by
-- proof
  intro r d
  have := riemann_roch_curves_thm 0 χ (by simpa using hχ_struct) hχ_sky r d
  simpa using this

end RiemannRochCurves

namespace RiemannRochCurves

/--
[idealDeg_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma idealDeg_top
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A] :
-- imply
  idealDeg k A ⊤ = 0 := by
-- proof
  unfold idealDeg
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

end RiemannRochCurves

namespace RiemannRochCurves

/--
[idealDeg_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
lemma idealDeg_bot
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A] :
-- imply
  idealDeg k A ⊥ = Module.finrank k A := by
-- proof
  unfold idealDeg
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k A).toLinearEquiv]

end RiemannRochCurves

/--
[rr_value_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
private lemma rr_value_structure_sheaf_eq
  {g : ℤ} :
-- imply
  rrHom g (1, 0) = 1 - g := by
-- proof
  apply RiemannRochCurves.rr_value_structure_sheaf g

/--
[rr_value_skyscraper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochCurves.lean)
-/
@[path]
private lemma rr_value_skyscraper_eq
  {g : ℤ} :
-- imply
  rrHom g (0, 1) = 1 := by
-- proof
  apply RiemannRochCurves.rr_value_skyscraper g


-- created on 2026-10-23
