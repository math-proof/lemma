import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.RefinementFrame
open GLnBuilding


/--
[CompleteFlag.IsStrictFlag.spaces_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  σ.spaces ⟨i.val, by omega⟩ < σ.spaces ⟨i.val + 1, by omega⟩ := by
-- proof
  rw [lt_iff_le_and_ne]
  constructor
  · exact σ.monotone (Fin.mk_le_mk.mpr (by omega))
  · intro h
    have h1 := hσ ⟨i.val, by omega⟩
    have h2 := hσ ⟨i.val + 1, by omega⟩
    simp only at h1 h2
    rw [h] at h1; omega



/--
[CompleteFlag.IsStrictFlag.gapVector_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.gapVector_mem
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  hσ.gapVector i ∈ σ.spaces ⟨i.val + 1, by omega⟩ :=
-- proof
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose_spec.1



/--
[CompleteFlag.IsStrictFlag.gapVector_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.gapVector_not_mem
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  hσ.gapVector i ∉ σ.spaces ⟨i.val, by omega⟩ :=
-- proof
  (SetLike.exists_of_lt (hσ.spaces_lt i)).choose_spec.2



/--
[CompleteFlag.IsStrictFlag.gapVector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.gapVector_ne_zero
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {i : Fin n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  hσ.gapVector i ≠ 0 := by
-- proof
  intro h
  exact hσ.gapVector_not_mem i (h ▸ zero_mem _)



/--
[CompleteFlag.IsStrictFlag.gapVector_mem_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.gapVector_mem_of_le
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {i : Fin n}
  {j : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hij : i.val + 1 ≤ j.val) :
-- imply
  hσ.gapVector i ∈ σ.spaces j :=
-- proof
  σ.monotone (Fin.mk_le_mk.mpr hij) (hσ.gapVector_mem i)



/--
[CompleteFlag.IsStrictFlag.linearIndependent_gapVectors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.linearIndependent_gapVectors
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  LinearIndependent k (fun i : Fin n => hσ.gapVector i) := by
-- proof
  suffices ∀ (m : ℕ) (hm : m ≤ n),
    LinearIndependent k (fun i : Fin m => hσ.gapVector ⟨i.val, by omega⟩) by
    have h := this n le_rfl
    convert h using 1
  intro m
  induction m with
  | zero => intro _; exact linearIndependent_empty_type
  | succ p ih =>
    intro hp
    rw [linearIndependent_fin_succ']
    constructor
    ·
      convert ih (by omega) using 1
    ·
      intro hmem
      have hspan_le : Submodule.span k (Set.range (Fin.init (fun i : Fin (p + 1) =>
        hσ.gapVector ⟨i.val, by omega⟩))) ≤ σ.spaces ⟨p, by omega⟩ := by
        rw [Submodule.span_le]
        rintro x ⟨⟨j, hj⟩, rfl⟩
        simp only [Fin.init]
        exact hσ.gapVector_mem_of_le ⟨j, by omega⟩ ⟨p, by omega⟩ (by simp; omega)
      exact hσ.gapVector_not_mem ⟨p, by omega⟩ (hspan_le hmem)



/--
[CompleteFlag.IsStrictFlag.span_gapVectors_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementFrame.lean)
-/
private lemma CompleteFlag.IsStrictFlag.span_gapVectors_eq_top
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  [FiniteDimensional k (Vec k n)]
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  Submodule.span k (Set.range (fun i : Fin n => hσ.gapVector i)) = ⊤ := by
-- proof
  apply hσ.linearIndependent_gapVectors.span_eq_top_of_card_eq_finrank'
  simp



-- created on 2026-10-23
-- updated on 2026-10-24
