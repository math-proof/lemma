import Mathlib
import sympy.Basic
import Lemma.Matrix.Eq.of.Offset.Normal.AffineHyperplaneE
open Set AffineWeylGroupFullData
open scoped InnerProductSpace


/--
[affineWeylGroup_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma affineWeylGroup_locallyFinite
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  d.affineArr.IsLocallyFinite :=
-- proof
  proposition_locallyFinite

/--
[affineWeylGroup_semidirectProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma affineWeylGroup_semidirectProduct
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E, ∃ (t : E), t ∈ d.corootLattice ∧ d.affineReflFun α k v = d.linearReflFun α v + t) ∧ (∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice, (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice) ∧ (∀ (w : E ≃ₗᵢ[ℝ] E) (t : E), (∀ v : E, w v = v + t) → t = 0 ∧ w = 1) :=
-- proof
  proposition_semidirectProduct

/--
[affineWeylGroup_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma affineWeylGroup_stable
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  (∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = η.normal ∧ ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier) ∧ (∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧ η'.offset = η.offset) :=
-- proof
  proposition_stable

/--
[coroot_translation_eq_composition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma coroot_translation_eq_composition
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) :=
-- proof
  corootTranslation_eq_comp_affineRefls hα


-- created on 2026-10-23
-- updated on 2026-10-24
