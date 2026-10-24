/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ModularForms/MeromorphicAtCusps.lean -/


import sympy.atlas.NumberTheory.ModularForms.MeromorphicAtCusps
import Lemma.Nat.ModularForms.MeromorphicAtCusps


open scoped UpperHalfPlane MatrixGroups

example (c : ℂ) : ModularFunction.IsMeromorphicAtInfty (fun _ ↦ c) :=
  ⟨1, Nat.one_pos, fun _ ↦ c, MeromorphicAt.const c 0,
    Filter.Eventually.of_forall fun _ ↦ rfl⟩

example : ModularFunction.IsMeromorphicAtInfty
    (fun τ : ℍ ↦ Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) :=
  ⟨(1 : ℕ), Nat.one_pos, (id : ℂ → ℂ), MeromorphicAt.id (0 : ℂ),
    Filter.Eventually.of_forall fun _ ↦ by simp⟩

example (c : ℂ) : ModularFunction.IsMeromorphicAtCusps (fun _ ↦ c) :=
  fun _ ↦ ⟨1, Nat.one_pos, fun _ ↦ c, MeromorphicAt.const c 0,
    Filter.Eventually.of_forall fun _ ↦ rfl⟩

example {f : ℍ → ℂ} (hf : ModularFunction.IsMeromorphicAtCusps f) :
    ModularFunction.IsMeromorphicAtInfty f :=
  hf.at_infty
