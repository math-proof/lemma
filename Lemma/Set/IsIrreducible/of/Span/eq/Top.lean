import Mathlib
import sympy.Basic

open Module LinearMap

/--
[Representation_isIrreducible_of_span_range_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_isIrreducible_of_span_range_eq_top.lean)
-/
@[main]
private lemma main
  [Field k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V]
  {ρ : Representation k G V}
-- given
  (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) :
-- imply
  ρ.IsIrreducible := by
-- proof
  have hstable : ∀ (W : Subrepresentation ρ) (f : Module.End k V) ⦃v : V⦄,
      v ∈ W.toSubmodule → f v ∈ W.toSubmodule := by
    intro W f
    have hf : f ∈ Submodule.span k (Set.range ⇑ρ) := hspan ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact W.apply_mem_toSubmodule g
    | zero =>
      intro v _
      simp
    | add x y _ _ hx hy =>
      intro v hv
      simpa using W.toSubmodule.add_mem (hx hv) (hy hv)
    | smul a x _ hx =>
      intro v hv
      simpa using W.toSubmodule.smul_mem a (hx hv)
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule k V) (congrArg Subrepresentation.toSubmodule h)⟩
  refine IsSimpleOrder.of_forall_eq_top fun W hW => ?_
  apply Subrepresentation.toSubmodule_injective
  show W.toSubmodule = ⊤
  have hWbot : W.toSubmodule ≠ ⊥ := fun h =>
    hW (Subrepresentation.toSubmodule_injective (h.trans rfl))
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  rw [Submodule.eq_top_iff']
  intro v
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hw0
  have hfw : (LinearMap.smulRight φ v) w = v := by
    rw [LinearMap.smulRight_apply, hφ, one_smul]
  exact hfw ▸ hstable W (LinearMap.smulRight φ v) hwW


-- created on 2026-10-05
