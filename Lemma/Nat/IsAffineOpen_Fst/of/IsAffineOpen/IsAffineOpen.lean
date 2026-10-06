import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage.lean)
-/
@[main]
private lemma main
  {X Y S : Scheme.{u}} [IsAffine S]
  {f : X ⟶ S}
  {g : Y ⟶ S}
  {U : X.Opens}
  {V : Y.Opens}
-- given
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
-- imply
  IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
-- proof
  let φ := pullback.map (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) f g hU.fromSpec hV.fromSpec (𝟙 S)
    (by simp) (by simp)
  have hrange : Scheme.Hom.opensRange φ = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext x
    show x ∈ Set.range φ ↔ x ∈ ((pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : (pullback f g).Opens) : Set _)
    rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]
    rfl
  rw [← hrange]
  exact isAffineOpen_opensRange φ


-- created on 2026-10-05
