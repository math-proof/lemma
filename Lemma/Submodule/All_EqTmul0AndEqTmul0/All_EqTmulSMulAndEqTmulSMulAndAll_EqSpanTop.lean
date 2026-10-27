import Mathlib
import Initialize.Tactic.Attr.Basic
open TensorProduct Module


/--
[tensorProduct_proposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DehnInvariant.lean)
-/
@[path]
private lemma main
  {G : Type u} [AddCommGroup G]
  {H : Type v} [AddCommGroup H] :
-- imply
  (∀ (g : G) (h : H), (0 : G) ⊗ₜ[ℤ] h = 0 ∧ g ⊗ₜ[ℤ] (0 : H) = 0) ∧
    (∀ (a : ℤ) (g : G) (h : H), (a • g) ⊗ₜ[ℤ] h = a • (g ⊗ₜ[ℤ] h) ∧
      g ⊗ₜ[ℤ] (a • h) = a • (g ⊗ₜ[ℤ] h)) ∧
    (∀ (s : Set G) (t : Set H), Submodule.span ℤ s = ⊤ → Submodule.span ℤ t = ⊤ →
      Submodule.span ℤ (Set.image2 (fun g h => g ⊗ₜ[ℤ] h) s t) = ⊤) := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  ·
    intro g h
    refine ⟨TensorProduct.zero_tmul G h, TensorProduct.tmul_zero H g⟩
  ·
    intro a g h
    refine ⟨(TensorProduct.smul_tmul' a g h).symm, TensorProduct.tmul_smul a g h⟩
  ·
    intro s t hs ht
    have h1 := Submodule.map₂_span_span ℤ (TensorProduct.mk ℤ G H) s t
    rw [hs, ht, TensorProduct.map₂_mk_top_top_eq_top] at h1
    show Submodule.span ℤ (Set.image2 (fun m n => (TensorProduct.mk ℤ G H m) n) s t) = ⊤
    apply h1.symm


-- created on 2026-10-23
-- updated on 2026-10-26
