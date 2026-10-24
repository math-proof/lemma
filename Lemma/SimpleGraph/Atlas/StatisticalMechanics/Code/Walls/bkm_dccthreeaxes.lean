import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bkm_dccthreeaxes
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[origin_mem_corridorRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma origin_mem_corridorRay_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (0 : Site d) ∈ corridorRay j := by
-- proof
  apply StatMech.Walls.origin_mem_corridorRay j

/--
[rayPt_mem_corridorRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma rayPt_mem_corridorRay_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ} :
-- imply
  hrHD_rayPt j t ∈ corridorRay j := by
-- proof
  apply StatMech.Walls.rayPt_mem_corridorRay j t

/--
[corridorEdge_subset_corridorRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma corridorEdge_subset_corridorRay_eq
  {d : ℕ}
  {j : Fin d}
  {t : ℤ} :
-- imply
  ∀ y ∈ (s(hrHD_rayPt j t, hrHD_rayPt j (t + 1)) : Sym2 (Site d)), y ∈ corridorRay j := by
-- proof
  apply StatMech.Walls.corridorEdge_subset_corridorRay t

/--
[bkm_three_axes_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma bkm_three_axes_distinct_eq
  {d : ℕ}
-- given
  (hd : 3 ≤ d) :
-- imply
  (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ ∧ (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ ∧ (⟨1, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by
-- proof
  apply StatMech.Walls.bkm_three_axes_distinct hd

/--
[bkm_corridorRay_inter_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma bkm_corridorRay_inter_eq_origin_eq
  {d : ℕ}
  {i j : Fin d}
-- given
  (h : i ≠ j) :
-- imply
  corridorRay i ∩ corridorRay j = {(0 : Site d)} := by
-- proof
  apply StatMech.Walls.bkm_corridorRay_inter_eq_origin h

/--
[bkm_corridorRay_disjoint_off_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma bkm_corridorRay_disjoint_off_origin_eq
  {d : ℕ}
  {i j : Fin d}
  {x : Site d}
-- given
  (h : i ≠ j)
  (hx : x ≠ 0) :
-- imply
  ¬ (x ∈ corridorRay i ∧ x ∈ corridorRay j) := by
-- proof
  apply StatMech.Walls.bkm_corridorRay_disjoint_off_origin h hx

/--
[bkm_corridorEdges_disjoint_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma bkm_corridorEdges_disjoint_of_ne_eq
  {d : ℕ}
  {i j : Fin d}
  {L : ℕ}
-- given
  (h : i ≠ j) :
-- imply
  Disjoint (hrHD_corridorEdges i L) (hrHD_corridorEdges j L) := by
-- proof
  apply StatMech.Walls.bkm_corridorEdges_disjoint_of_ne h L

/--
[bkm_dcc_three_axes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean)
-/
@[path]
private lemma bkm_dcc_three_axes_eq
  {d : ℕ}
-- given
  (hd : 3 ≤ d) :
-- imply
  ∃ j₁ j₂ j₃ : Fin d, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧ (corridorRay j₁ ∩ corridorRay j₂ = {(0 : Site d)} ∧ corridorRay j₁ ∩ corridorRay j₃ = {(0 : Site d)} ∧ corridorRay j₂ ∩ corridorRay j₃ = {(0 : Site d)}) ∧ (∀ L : ℕ, Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₂ L) ∧ Disjoint (hrHD_corridorEdges j₁ L) (hrHD_corridorEdges j₃ L) ∧ Disjoint (hrHD_corridorEdges j₂ L) (hrHD_corridorEdges j₃ L)) := by
-- proof
  apply StatMech.Walls.bkm_dcc_three_axes hd


-- created on 2026-10-23
