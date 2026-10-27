import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.InteriorCells.Part2
open StatMech StatMech.Onsager StatMech.Onsager.InteriorCells


/--
[yInf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma yInf_le_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n} :
-- imply
  yInf d ≤ (pos d k).2 := by
-- proof
  apply StatMech.Onsager.InteriorCells.yInf_le d k

/--
[le_ySup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma le_ySup_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n} :
-- imply
  (pos d k).2 ≤ ySup d := by
-- proof
  apply StatMech.Onsager.InteriorCells.le_ySup d k

/--
[exists_edge_of_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma exists_edge_of_rayParity_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (h : rayParity d a b = 1) :
-- imply
  ∃ k : Fin n, isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ b < (pos d k).2 := by
-- proof
  apply StatMech.Onsager.InteriorCells.exists_edge_of_rayParity d a b h

/--
[rayParity_zero_of_lt_yInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma rayParity_zero_of_lt_yInf_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hb : b < yInf d) :
-- imply
  rayParity d a b = 0 := by
-- proof
  apply StatMech.Onsager.InteriorCells.rayParity_zero_of_lt_yInf d hclosed a b hb

/--
[interiorSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma interiorSet_finite_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (interiorSet d).Finite := by
-- proof
  apply StatMech.Onsager.InteriorCells.interiorSet_finite d hclosed

/--
[mem_interiorCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean)
-/
@[path]
private lemma mem_interiorCells_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {c : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  c ∈ interiorCells d hclosed ↔ rayParity d c.1 c.2 = 1 := by
-- proof
  apply StatMech.Onsager.InteriorCells.mem_interiorCells d hclosed c


-- created on 2026-10-23
