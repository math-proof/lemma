/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.Tactic.Group
import Def.v1.Atlas.Buildings.code.BNPair.CellMulFiniteProof
set_option linter.unusedSectionVars false

open scoped Classical

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace CellMulFinite

open BNPair

/-- $C(w) \cdot C(s) \subseteq C(ws) \cup C(w)$: the product is covered by at most two cells. -/
theorem setMul_bruhatCell_simple_subset (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w : M.Group) (s : B_idx) :
    setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      ⋃ u ∈ setMul_bruhatCell_simple_finset bp ax w s, bp.bruhatCell u := by
  let cs := M.toCoxeterSystem
  intro g hg
  rcases cs.length_mul_simple w s with hlen | hlen
  ·
    have hgt : cs.length (w * cs.simple s) > cs.length w := by omega
    simp only [setMul_bruhatCell_simple_finset, Finset.mem_insert, Finset.mem_singleton,
      Set.mem_iUnion, exists_prop]
    exact ⟨w * cs.simple s, Or.inl rfl, ax.cell_mul_length_increasing w s hgt hg⟩
  ·
    have hlt : cs.length (w * cs.simple s) < cs.length w := by omega
    simp only [setMul_bruhatCell_simple_finset, Finset.mem_insert, Finset.mem_singleton,
      Set.mem_iUnion, exists_prop]
    rcases ax.cell_mul_length_decreasing w s hlt hg with h | h
    · exact ⟨w * cs.simple s, Or.inl rfl, h⟩
    · exact ⟨w, Or.inr rfl, h⟩

/-- Right $B$-absorption: $C(w) \cdot B \subseteq C(w)$. -/
theorem bruhatCell_mul_B_right (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    g * b ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

/-- $C(1) \subseteq B$: the identity Bruhat cell is contained in $B$. -/
theorem bruhatCell_one_sub_B (bp : BNPair G M) :
    bp.bruhatCell 1 ⊆ (bp.B : Set G) := by
  intro g hg
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  have n_in_T : (n : G) ∈ bp.T := (bp.π_ker n).mp hπ
  have n_in_B : (n : G) ∈ bp.B := by
    rw [bp.T_eq] at n_in_T; exact (Subgroup.mem_inf.mp n_in_T).1
  rw [hg_eq]
  exact bp.B.mul_mem (bp.B.mul_mem hb₁ n_in_B) hb₂

/-- Right neutrality at the cell level: $C(w) \cdot C(1) \subseteq C(w)$. -/
theorem setMul_bruhatCell_one (bp : BNPair G M) (w : M.Group) :
    setMul (bp.bruhatCell w) (bp.bruhatCell 1) ⊆ bp.bruhatCell w := by
  intro g ⟨x, hx, y, hy, hg_eq⟩
  have hy_B : y ∈ (bp.B : Set G) := bruhatCell_one_sub_B bp hy
  rw [hg_eq]
  exact bruhatCell_mul_B_right bp hx hy_B

/-- Inductive step for cell-product finiteness: if $C(w_0) \cdot C(w')$ is covered by finitely
many cells, then so is $C(w_0) \cdot C(w' s)$ for any simple $s$. -/
theorem extend_finite_cover (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w' : M.Group) (s : B_idx)
    (w₀ : M.Group)
    (us : Finset M.Group)
    (h_IH : setMul (bp.bruhatCell w₀) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u) :
    ∃ (us' : Finset M.Group),
      setMul (bp.bruhatCell w₀) (bp.bruhatCell (w' * M.toCoxeterSystem.simple s)) ⊆
        ⋃ u ∈ us', bp.bruhatCell u := by

  have h_factor : bp.bruhatCell (w' * M.toCoxeterSystem.simple s) ⊆
      setMul (bp.bruhatCell w') (bp.bruhatCell (M.toCoxeterSystem.simple s)) :=
    bruhatCell_sub_setMul bp w' (M.toCoxeterSystem.simple s)

  have h_assoc : setMul (bp.bruhatCell w₀) (bp.bruhatCell (w' * M.toCoxeterSystem.simple s)) ⊆
      setMul (setMul (bp.bruhatCell w₀) (bp.bruhatCell w'))
        (bp.bruhatCell (M.toCoxeterSystem.simple s)) := by
    calc setMul (bp.bruhatCell w₀) (bp.bruhatCell (w' * M.toCoxeterSystem.simple s))
        ⊆ setMul (bp.bruhatCell w₀)
            (setMul (bp.bruhatCell w') (bp.bruhatCell (M.toCoxeterSystem.simple s))) :=
          setMul_mono_right h_factor
      _ = setMul (setMul (bp.bruhatCell w₀) (bp.bruhatCell w'))
            (bp.bruhatCell (M.toCoxeterSystem.simple s)) :=
          (setMul_assoc _ _ _).symm

  have h_expand : setMul (setMul (bp.bruhatCell w₀) (bp.bruhatCell w'))
      (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      ⋃ u ∈ us, setMul (bp.bruhatCell u) (bp.bruhatCell (M.toCoxeterSystem.simple s)) := by
    rw [← setMul_biUnion_left]
    exact setMul_mono_left h_IH

  have h_bn2 : ⋃ u ∈ us,
      setMul (bp.bruhatCell u) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆
      ⋃ u ∈ us, ⋃ v ∈ setMul_bruhatCell_simple_finset bp ax u s, bp.bruhatCell v := by
    apply Set.iUnion₂_mono
    intro u _
    exact setMul_bruhatCell_simple_subset bp ax u s

  let us' : Finset M.Group := us ∪ us.image (· * M.toCoxeterSystem.simple s)
  refine ⟨us', ?_⟩
  calc setMul (bp.bruhatCell w₀) (bp.bruhatCell (w' * M.toCoxeterSystem.simple s))
      ⊆ setMul (setMul (bp.bruhatCell w₀) (bp.bruhatCell w'))
          (bp.bruhatCell (M.toCoxeterSystem.simple s)) := h_assoc
    _ ⊆ ⋃ u ∈ us,
          setMul (bp.bruhatCell u) (bp.bruhatCell (M.toCoxeterSystem.simple s)) := h_expand
    _ ⊆ ⋃ u ∈ us, ⋃ v ∈ setMul_bruhatCell_simple_finset bp ax u s, bp.bruhatCell v := h_bn2
    _ ⊆ ⋃ v ∈ us', bp.bruhatCell v := by
        intro g hg
        simp only [Set.mem_iUnion, exists_prop] at hg ⊢
        obtain ⟨u, hu, v, hv, hg⟩ := hg
        refine ⟨v, ?_, hg⟩
        simp only [setMul_bruhatCell_simple_finset, Finset.mem_insert, Finset.mem_singleton]
          at hv
        simp only [us', Finset.mem_union, Finset.mem_image]
        rcases hv with rfl | rfl
        · exact Or.inr ⟨u, hu, rfl⟩
        · exact Or.inl hu

/-- *Finiteness of cell products*: for any $w, w' \in W$, the product $C(w) \cdot C(w')$
is contained in a *finite* union $\bigcup_{u \in U} C(u)$ of Bruhat cells. -/
theorem cell_mul_finite_from_bnpair (bp : BNPair G M) (ax : BNPairAxioms bp)
    (w w' : M.Group) :
    ∃ (us : Finset M.Group),
      setMul (bp.bruhatCell w) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u := by
  let cs := M.toCoxeterSystem

  have hgen : Subgroup.closure (Set.range cs.simple) = ⊤ :=
    cs.subgroup_closure_range_simple
  have hw'_mem : w' ∈ Subgroup.closure (Set.range cs.simple) :=
    hgen ▸ Subgroup.mem_top _

  suffices ∀ (w' : M.Group), w' ∈ Subgroup.closure (Set.range cs.simple) →
      ∀ (w₀ : M.Group),
        ∃ (us : Finset M.Group),
          setMul (bp.bruhatCell w₀) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u by
    exact this w' hw'_mem w
  intro w' hw'
  refine Subgroup.closure_induction_right
    (p := fun (w' : M.Group) _ =>
      ∀ (w₀ : M.Group),
        ∃ (us : Finset M.Group),
          setMul (bp.bruhatCell w₀) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u)
    ?one ?mul_right ?mul_inv hw'
  ·
    intro w₀
    exact ⟨{w₀}, fun g hg => by
      simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop]
      exact ⟨w₀, rfl, setMul_bruhatCell_one bp w₀ hg⟩⟩
  ·
    intro w' _ si hsi IH w₀
    obtain ⟨i, rfl⟩ := hsi
    obtain ⟨us, hus⟩ := IH w₀
    exact extend_finite_cover bp ax w' i w₀ us hus
  ·

    intro w' _ si hsi IH w₀
    obtain ⟨i, rfl⟩ := hsi
    have simple_inv : (cs.simple i)⁻¹ = cs.simple i := by
      have h := cs.simple_mul_simple_cancel_left (w := 1) i
      rw [mul_one] at h
      exact inv_eq_of_mul_eq_one_right h
    rw [simple_inv]
    obtain ⟨us, hus⟩ := IH w₀
    exact extend_finite_cover bp ax w' i w₀ us hus

end CellMulFinite
