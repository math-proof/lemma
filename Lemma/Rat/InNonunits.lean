import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma mem_nonunits_iff_mem_and
  {K : Type} [Field K] (W : ValuationSubring K) (f : K) :
  f ∈ W.nonunits ↔ f ∈ W ∧ (f = 0 ∨ f⁻¹ ∉ W) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  ·
    intro hlt
    have hf : f ∈ W := (ValuationSubring.valuation_le_one_iff _ _).mp hlt.le
    refine ⟨hf, ?_⟩
    if hf0 : f = 0 then
      refine Or.inl hf0
    else
      right
      intro hinv
      have hunit : IsUnit (⟨f, hf⟩ : ↥W) :=
        isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩
      have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
      have h1' : W.valuation f = 1 := h1
      rw [h1'] at hlt
      refine lt_irrefl _ hlt
  ·
    intro h
    obtain ⟨hf, hor⟩ := h
    cases hor
    ·
      rename_i hf0
      rw [hf0, map_zero]
      refine zero_lt_one
    ·
      rename_i hinv
      cases ValuationSubring.valuation_lt_one_or_eq_one W ⟨f, hf⟩
      ·
        rename_i hlt
        refine hlt
      ·
        rename_i h1
        exfalso
        have hunit : IsUnit (⟨f, hf⟩ : ↥W) := (ValuationSubring.valuation_eq_one_iff _ _).mpr h1
        obtain ⟨g, hg⟩ := hunit.exists_right_inv
        have hg1 : f * (g : K) = 1 := congrArg Subtype.val hg
        have hf0 : f ≠ 0 := left_ne_zero_of_mul (hg1.trans_ne one_ne_zero)
        have hg2 : (g : K) = f⁻¹ := by
          rw [← mul_one f⁻¹, ← hg1, inv_mul_cancel_left₀ hf0]
        refine hinv (hg2 ▸ g.2)
/--
[ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff.lean)
-/
@[path]
private lemma main
  (K K' : Type) [Field K] [Field K'] (ι : K →+* K')
  (W : ValuationSubring K) (W' : ValuationSubring K')
  (h : ∀ f : K, f ∈ W ↔ ι f ∈ W') (f : K) :
  -- imply
  f ∈ W.nonunits ↔ ι f ∈ W'.nonunits := by
  -- proof
  rw [mem_nonunits_iff_mem_and W f, mem_nonunits_iff_mem_and W' (ι f), h f, h f⁻¹, map_inv₀,
    map_eq_zero_iff ι ι.injective]


-- created on 2026-10-20
