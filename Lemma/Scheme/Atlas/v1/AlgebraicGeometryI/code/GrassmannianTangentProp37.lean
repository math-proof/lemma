import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GrassmannianTangentProp37


/--
[grassmannianChart_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean)
-/
@[path]
lemma grassmannianChart_zero
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  grassmannianChart V V' hc 0 = V := by
-- proof
  ext w
  simp only [grassmannianChart, Submodule.mem_map, LinearMap.mem_graph_iff,
    LinearMap.zero_apply, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨⟨a, b⟩, hb, heq⟩
    change b = 0 at hb
    subst hb
    simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero] at heq
    rw [← heq]; exact a.2
  · intro hw
    exact ⟨⟨⟨w, hw⟩, 0⟩, rfl, by
      simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]⟩

/--
[grassmannianChart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean)
-/
@[path]
lemma grassmannianChart_injective
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  Function.Injective (grassmannianChart V V' hc) := by
-- proof
  intro φ ψ h
  simp only [grassmannianChart] at h
  have hinj := (Submodule.prodEquivOfIsCompl V V' hc).injective
  have hgraph : LinearMap.graph φ = LinearMap.graph ψ :=
    Submodule.map_injective_of_injective hinj h
  ext v
  have hmem : (v, φ v) ∈ LinearMap.graph ψ :=
    hgraph ▸ (LinearMap.mem_graph_iff φ _).2 rfl
  exact congr_arg Subtype.val ((LinearMap.mem_graph_iff ψ _).1 hmem)

/--
[proposition_37_tangent_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean)
-/
@[path]
lemma proposition_37_tangent_space
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  Nonempty ((V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V))) :=
-- proof
  ⟨grassmannianTangentIso V V' hc⟩

/--
[proposition_37_cotangent_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean)
-/
@[path]
lemma proposition_37_cotangent_space
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  Nonempty ((V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V)) :=
-- proof
  ⟨grassmannianCotangentIso V V' hc⟩

/--
[proposition_37_complement_independence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean)
-/
@[path]
lemma proposition_37_complement_independence
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V'₁ V'₂ : Submodule F W}
-- given
  (h₁ : IsCompl V V'₁)
  (h₂ : IsCompl V V'₂) :
-- imply
  Nonempty ((V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂)) :=
-- proof
  ⟨grassmannianTangentIso_independence V V'₁ V'₂ h₁ h₂⟩


-- created on 2026-10-23
