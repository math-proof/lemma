import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
open DifferentialFormSpace


/--
[pullback_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean)
-/
@[path]
lemma pullback_neg
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ}
  {α : Ω₂ p} :
-- imply
  φ.pullback (-α) = -(φ.pullback α) := by
-- proof
  have h := φ.pullback_smul (-1 : ℝ) α
  simp only [neg_smul, one_smul] at h
  exact h

/--
[pullback_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean)
-/
@[path]
lemma pullback_sub
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ}
  {α β : Ω₂ p} :
-- imply
  φ.pullback (α - β) = φ.pullback α - φ.pullback β := by
-- proof
  rw [sub_eq_add_neg, φ.pullback_add, pullback_neg, ← sub_eq_add_neg]

/--
[graph_lagrangian_of_symplectomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean)
-/
@[path]
lemma graph_lagrangian_of_symplectomorphism
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  {Ω_P : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  [inst_P : DifferentialFormSpace Ω_P VF_P]
  {S₁ : SymplecticManifold Ω₁ VF₁}
  {S₂ : SymplecticManifold Ω₂ VF₂}
  {G : GraphSetup Ω₁ VF₁ Ω₂ VF₂ Ω_P VF_P S₁ S₂}
-- given
  (hφ : G.φ.pullback S₂.ω = S₁.ω) :
-- imply
  G.γ.pullback (G.π₁.pullback S₁.ω - G.π₂.pullback S₂.ω) = (0 : Ω₁ 2) := by
-- proof
  rw [pullback_sub (inst₂ := inst_P), G.γ_π₁, G.γ_π₂, hφ, sub_self]

/--
[symplectomorphism_of_graph_lagrangian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean)
-/
@[path]
lemma symplectomorphism_of_graph_lagrangian
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  {Ω_P : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  [inst_P : DifferentialFormSpace Ω_P VF_P]
  {S₁ : SymplecticManifold Ω₁ VF₁}
  {S₂ : SymplecticManifold Ω₂ VF₂}
  {G : GraphSetup Ω₁ VF₁ Ω₂ VF₂ Ω_P VF_P S₁ S₂}
-- given
  (hLag : G.γ.pullback (G.π₁.pullback S₁.ω - G.π₂.pullback S₂.ω) = (0 : Ω₁ 2)) :
-- imply
  G.φ.pullback S₂.ω = S₁.ω := by
-- proof
  rw [pullback_sub (inst₂ := inst_P), G.γ_π₁, G.γ_π₂] at hLag
  exact (sub_eq_zero.mp hLag).symm


-- created on 2026-10-23
