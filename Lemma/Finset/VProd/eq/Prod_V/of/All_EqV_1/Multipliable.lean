import Mathlib
import sympy.Basic
open scoped Topology
open Filter


/--
[Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.lean)
-/
@[path]
private lemma main
  [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {f : ι → K}
  {S : Finset ι}
-- given
  (hf : Multipliable f)
  (hS : ∀ i, i ∉ S → Valued.v (f i) = 1) :
-- imply
  Valued.v (∏' i, f i) = ∏ i ∈ S, Valued.v (f i) := by
-- proof
  classical
    have hprod := hf.hasProd
    have hpart : ∀ T : Finset ι, S ⊆ T → Valued.v (∏ i ∈ T, f i) = Valued.v (∏ i ∈ S, f i) := by
      intro T hT
      rw [map_prod, map_prod, ← Finset.prod_sdiff hT, Finset.prod_eq_one (fun i hi => hS i (Finset.mem_sdiff.mp hi).2),
        one_mul]
    have hres : ∀ x y : K, Valued.v x = Valued.v y ↔
        (Valued.v : Valuation K Γ₀).restrict x = (Valued.v : Valuation K Γ₀).restrict y := by
      intro x y
      constructor
      ·
        intro h
        apply le_antisymm
        · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
        · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
      ·
        intro h
        apply le_antisymm
        · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]
        · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]
    have hclosed := Valued.isClosed_sphere (R := K) ((Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f i))
    have hev : ∀ᶠ T : Finset ι in atTop,
        (∏ i ∈ T, f i) ∈ {x : K | (Valued.v : Valuation K Γ₀).restrict x =
          (Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f i)} := by
      filter_upwards [eventually_ge_atTop S] with T hT
      exact (hres _ _).mp (hpart T hT)
    have hmem := hclosed.mem_of_tendsto hprod hev
    rw [Set.mem_setOf_eq] at hmem
    rw [(hres _ _).mpr hmem, map_prod]


-- created on 2026-10-23
