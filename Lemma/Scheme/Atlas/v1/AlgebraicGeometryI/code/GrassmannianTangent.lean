import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GrassmannianTangent.Part2
open Module (finrank) Grassmannian


namespace Grassmannian

/--
[chart_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma chart_zero
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  chart V V' hc 0 = V := by
-- proof
  ext w
  simp only [chart, Submodule.mem_map, LinearMap.mem_graph_iff,
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

end Grassmannian

namespace Grassmannian

/--
[chart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma chart_injective
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
-- given
  (hc : IsCompl V V') :
-- imply
  Function.Injective (chart V V' hc) := by
-- proof
  intro φ ψ h
  simp only [chart] at h
  have hinj := (Submodule.prodEquivOfIsCompl V V' hc).injective
  have hgraph : LinearMap.graph φ = LinearMap.graph ψ :=
    Submodule.map_injective_of_injective hinj h
  ext v
  have hmem : (v, φ v) ∈ LinearMap.graph ψ :=
    hgraph ▸ (LinearMap.mem_graph_iff φ _).2 rfl
  exact congr_arg Subtype.val ((LinearMap.mem_graph_iff ψ _).1 hmem)

end Grassmannian

namespace Grassmannian

/--
[tangentSpaceIso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma tangentSpaceIso_apply
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V' : Submodule F W}
  {φ : V →ₗ[F] V'}
  {v : V}
-- given
  (hc : IsCompl V V') :
-- imply
  (tangentSpaceIso V V' hc φ) v = Submodule.mkQ V (φ v : W) := by
-- proof
  simp [tangentSpaceIso, LinearEquiv.arrowCongr_apply,
    Submodule.quotientEquivOfIsCompl]

end Grassmannian

namespace Grassmannian

/--
[tangentSpaceIso_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma tangentSpaceIso_independent
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V'₁ V'₂ : Submodule F W}
  {φ₁ : V →ₗ[F] V'₁}
  {φ₂ : V →ₗ[F] V'₂}
-- given
  (h₁ : IsCompl V V'₁)
  (h₂ : IsCompl V V'₂)
  (hcompat : ∀ v : V, Submodule.mkQ V (φ₁ v : W) = Submodule.mkQ V (φ₂ v : W)) :
-- imply
  tangentSpaceIso V V'₁ h₁ φ₁ = tangentSpaceIso V V'₂ h₂ φ₂ := by
-- proof
  ext v
  rw [tangentSpaceIso_apply, tangentSpaceIso_apply]
  exact hcompat v

end Grassmannian

namespace Grassmannian

/--
[complementChangeIso_factors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma complementChangeIso_factors
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {V V'₁ V'₂ : Submodule F W}
  {φ : V →ₗ[F] V'₁}
-- given
  (h₁ : IsCompl V V'₁)
  (h₂ : IsCompl V V'₂) :
-- imply
  tangentSpaceIso V V'₂ h₂ (complementChangeIso V V'₁ V'₂ h₁ h₂ φ) = tangentSpaceIso V V'₁ h₁ φ := by
-- proof
  simp [complementChangeIso, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end Grassmannian

namespace Grassmannian

/--
[tangent_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma tangent_finrank_eq
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V]
  {Sub : Submodule k V} :
-- imply
  finrank k (Sub →ₗ[k] (V ⧸ Sub)) = finrank k Sub * finrank k (V ⧸ Sub) :=
-- proof
  Module.finrank_linearMap k k Sub (V ⧸ Sub)

end Grassmannian

namespace Grassmannian

/--
[tangent_finrank_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma tangent_finrank_formula
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V]
  {Sub : Submodule k V} :
-- imply
  finrank k (Sub →ₗ[k] (V ⧸ Sub)) = finrank k Sub * (finrank k V - finrank k Sub) := by
-- proof
  rw [tangent_finrank_eq]
  congr 1
  have h := Sub.finrank_quotient_add_finrank
  omega

end Grassmannian

namespace Grassmannian

/--
[tangent_finrank_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma tangent_finrank_explicit
  [Field F]
  [AddCommGroup W]
  [Module F W]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V]
  {Sub : Submodule k V}
-- given
  (hd : finrank k Sub = d)
  (hn : finrank k V = n) :
-- imply
  finrank k (Sub →ₗ[k] (V ⧸ Sub)) = d * (n - d) := by
-- proof
  rw [tangent_finrank_formula, hd, hn]
end Grassmannian
section TangentCone


/--
[ideal_pow_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma ideal_pow_succ_le
  [CommRing R]
  {I : Ideal R}
  {n : ℕ} :
-- imply
  I ^ (n + 1) ≤ I ^ n :=
-- proof
  Ideal.pow_le_pow_right (Nat.le_succ n)

/--
[associatedGradedComponent.mk_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean)
-/
@[path]
lemma associatedGradedComponent.mk_surjective
  [CommRing R]
  {I : Ideal R}
  {n : ℕ} :
-- imply
  Function.Surjective (associatedGradedComponent.mk I n) :=
-- proof
  Submodule.mkQ_surjective _
end TangentCone


-- created on 2026-10-23
