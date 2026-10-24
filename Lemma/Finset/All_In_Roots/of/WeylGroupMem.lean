import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Theorems
open Set FiniteReflectionGroups
open scoped InnerProductSpace


/--
[RootSystem.weylGroupMem_maps_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Theorems.lean)
-/
@[path]
lemma RootSystem.weylGroupMem_maps_roots
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Φ : RootSystem E}
  {g : E → E}
-- given
  (hg : Φ.WeylGroupMem g) :
-- imply
  ∀ β ∈ Φ.roots, g β ∈ Φ.roots := by
-- proof
  induction hg with
  | id => intro β hβ; exact hβ
  | gen α hα => intro β hβ; exact Φ.reflection_closed α hα β hβ
  | comp f g _hf _hg ihf ihg => intro β hβ; exact ihf _ (ihg β hβ)


private lemma foldr_refl_comp_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {αs₁ αs₂ : List E}
  {x : E} :
-- imply
  (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id) ((αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) x) = ((αs₁ ++ αs₂).foldr (fun a f => linearReflection a ∘ f) _root_.id) x := by
-- proof
  induction αs₁ with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, Function.comp_apply, List.cons_append]; exact congr_arg _ ih


private lemma RootSystem.weylGroupMem_is_composition
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Φ : RootSystem E}
  {g : E → E}
-- given
  (hg : Φ.WeylGroupMem g) :
-- imply
  ∃ αs : List E, (∀ a ∈ αs, a ∈ Φ.roots) ∧ g = αs.foldr (fun a f => linearReflection a ∘ f) _root_.id := by
-- proof
  induction hg with
  | id => exact ⟨[], by simp, rfl⟩
  | gen α hα =>
    refine ⟨[α], fun a ha => ?_, by simp⟩
    simp at ha; subst ha; exact hα
  | comp f g _hf _hg ihf ihg =>
    obtain ⟨αs₁, h₁, rfl⟩ := ihf
    obtain ⟨αs₂, h₂, rfl⟩ := ihg
    refine ⟨αs₁ ++ αs₂, fun a ha => ?_, ?_⟩
    · rcases List.mem_append.mp ha with h | h
      · exact h₁ a h
      · exact h₂ a h
    · ext x; simp only [Function.comp_apply]; exact foldr_refl_comp_eq αs₁ αs₂ x


private lemma foldr_refl_is_linear
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {αs : List E} :
-- imply
  ∃ L : E →ₗ[ℝ] E, ∀ v, L v = (αs.foldr (fun a f => linearReflection a ∘ f) _root_.id) v := by
-- proof
  induction αs with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons a as ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨(linearReflectionLM a).comp L, fun v => ?_⟩
    simp only [LinearMap.comp_apply, linearReflectionLM_apply, List.foldr_cons,
      Function.comp_apply]
    rw [← hL]


private lemma foldr_refl_eq_of_agree_on_roots
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {αs₁ αs₂ : List E}
  {S : Set E}
-- given
  (hS : Submodule.span ℝ S = ⊤)
  (h : ∀ x ∈ S, (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id) x = (αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) x) :
-- imply
  (αs₁.foldr (fun a f => linearReflection a ∘ f) _root_.id) = (αs₂.foldr (fun a f => linearReflection a ∘ f) _root_.id) := by
-- proof
  obtain ⟨L₁, hL₁⟩ := foldr_refl_is_linear αs₁
  obtain ⟨L₂, hL₂⟩ := foldr_refl_is_linear αs₂
  have hLeq : L₁ = L₂ := by
    apply LinearMap.ext_on hS
    intro x hx
    rw [hL₁, hL₂]
    exact h x hx
  ext v
  rw [← hL₁ v, ← hL₂ v, hLeq]


private lemma restrictToRoots_val
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Φ : RootSystem E}
  {g : E → E}
  {β : ↥Φ.roots}
-- given
  (hg : Φ.WeylGroupMem g) :
-- imply
  (restrictToRoots Φ g β).val = g β.val := by
-- proof
  simp only [restrictToRoots]
  rw [dif_pos (Φ.weylGroupMem_maps_roots hg β.val β.prop)]


private lemma linearReflection_self
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {α : E}
-- given
  (hα : α ≠ 0) :
-- imply
  linearReflection α α = -α := by
-- proof
  simp only [linearReflection]
  have h : 2 * ⟪α, α⟫_ℝ / ⟪α, α⟫_ℝ = 2 := by
    rw [mul_div_cancel_of_imp]
    intro h; exact absurd (inner_self_eq_zero.mp h) hα
  rw [h, two_smul]; abel


private lemma RootSystem.neg_mem_roots
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Φ : RootSystem E}
  {α : E}
-- given
  (hα : α ∈ Φ.roots) :
-- imply
  -α ∈ Φ.roots := by
-- proof
  rw [← linearReflection_self α (Φ.roots_ne_zero α hα)]
  exact Φ.reflection_closed α hα α hα


private lemma foldr_comp_append
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {l₁ l₂ : List (α → α)} :
-- imply
  l₁.foldr (· ∘ ·) _root_.id ∘ l₂.foldr (· ∘ ·) _root_.id = (l₁ ++ l₂).foldr (· ∘ ·) _root_.id := by
-- proof
  induction l₁ with
  | nil => simp
  | cons f l₁ ih =>
    simp only [List.foldr_cons, List.cons_append]
    rw [← ih]; ext; simp [Function.comp]


private lemma ofFn_linearReflection_append
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {n₁ n₂ : ℕ}
  {αs₁ : Fin n₁ → E}
  {αs₂ : Fin n₂ → E} :
-- imply
  (List.ofFn fun i => linearReflection (Fin.append αs₁ αs₂ i)) = (List.ofFn fun i => linearReflection (αs₁ i)) ++ (List.ofFn fun i => linearReflection (αs₂ i)) := by
-- proof
  have : (fun i => linearReflection (Fin.append αs₁ αs₂ i)) =
    Fin.append (fun i => linearReflection (αs₁ i)) (fun i => linearReflection (αs₂ i)) := by
    ext i
    simp [Fin.append]
    exact Fin.addCases (fun j => by simp [Fin.addCases]) (fun j => by simp [Fin.addCases]) i
  rw [this, List.ofFn_fin_append]


private lemma RootSystem.list_foldr_weylGroupMem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {Φ : RootSystem E}
  {αs : List E}
-- given
  (hαs : ∀ a ∈ αs, a ∈ Φ.roots) :
-- imply
  Φ.WeylGroupMem (αs.foldr (fun a g => linearReflection a ∘ g) _root_.id) := by
-- proof
  induction αs with
  | nil => simpa using WeylGroupMem.id
  | cons a as ih =>
    simp only [List.foldr_cons]
    exact WeylGroupMem.comp _ _
      (WeylGroupMem.gen a (hαs a List.mem_cons_self))
      (ih (fun b hb => hαs b (List.mem_cons_of_mem a hb)))


-- created on 2026-10-24
