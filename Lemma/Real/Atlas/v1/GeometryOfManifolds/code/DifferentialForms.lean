import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
open DifferentialFormSpace


namespace DifferentialFormSpace

/--
[d_zero_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
lemma d_zero_val
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ} :
-- imply
  inst.d (0 : Ω p) = (0 : Ω (p + 1)) := by
-- proof
  have h := inst.d_smul (0 : ℝ) (0 : Ω p)
  simp [zero_smul] at h; exact h

end DifferentialFormSpace

namespace DifferentialFormSpace

/--
[exact_is_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
lemma exact_is_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (h : IsExact' VF α) :
-- imply
  IsClosed' VF α := by
-- proof
  obtain ⟨β, hβ⟩ := h
  unfold IsClosed'
  rw [hβ, inst.d_squared]

end DifferentialFormSpace

/--
[DFSMorphism.pullback_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
lemma DFSMorphism.pullback_closed
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ}
  {α : Ω₂ p}
-- given
  (h : DifferentialFormSpace.IsClosed' VF₂ α) :
-- imply
  DifferentialFormSpace.IsClosed' VF₁ (φ.pullback α) := by
-- proof
  unfold DifferentialFormSpace.IsClosed' at *
  rw [← φ.pullback_comm_d, h]
  have : φ.pullback (0 : Ω₂ (p + 1)) = 0 := by
    have := φ.pullback_smul (0 : ℝ) (0 : Ω₂ (p + 1))
    simp [zero_smul] at this; exact this
  exact this

/--
[DFSMorphism.pullback_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
lemma DFSMorphism.pullback_exact
  {Ω₁ : ℕ → Type*}
  {Ω₂ : ℕ → Type*}
  [inst₁ : DifferentialFormSpace Ω₁ VF₁]
  [inst₂ : DifferentialFormSpace Ω₂ VF₂]
  {φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂}
  {p : ℕ}
  {α : Ω₂ (p + 1)}
-- given
  (h : DifferentialFormSpace.IsExact' VF₂ α) :
-- imply
  DifferentialFormSpace.IsExact' VF₁ (φ.pullback α) := by
-- proof
  obtain ⟨β, hβ⟩ := h
  exact ⟨φ.pullback β, by rw [hβ, φ.pullback_comm_d]⟩

/--
[DFSMorphism.id_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
lemma DFSMorphism.id_pullback
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω p} :
-- imply
  (@DFSMorphism.id Ω VF inst).pullback α = α :=
-- proof
  rfl

/--
[fMul_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
private lemma fMul_zero_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {f : Ω 0} :
-- imply
  inst.fMul f (0 : Ω p) = 0 := by
-- proof
  apply DifferentialFormSpace.fMul_zero f

/--
[d_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
private lemma d_neg_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω p} :
-- imply
  inst.d (-α) = -(inst.d α) := by
-- proof
  apply DifferentialFormSpace.d_neg α

/--
[cartan_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
private lemma cartan_step_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {p : ℕ}
  {β : Ω (p + 1)}
-- given
  (ih : ∀ (γ : Ω p), inst.d (inst.L X γ) = inst.d (inst.ι X (inst.d γ))) :
-- imply
  inst.L X β = inst.d (inst.ι X β) + inst.ι X (inst.d β) := by
-- proof
  apply DifferentialFormSpace.cartan_step X ih β

/--
[cartan_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean)
-/
@[path]
private lemma cartan_formula_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  inst.L X α = inst.d (inst.ι X α) + inst.ι X (inst.d α) := by
-- proof
  apply DifferentialFormSpace.cartan_formula X α


-- created on 2026-10-23
