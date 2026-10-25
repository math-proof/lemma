import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh4_mem_bondCompOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_mem_bondCompOf_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W}
  {i : ι} :
-- imply
  i ∈ gh4_bondCompOf ends K u ↔ i ∈ K ∧ ∃ x ∈ ends i, connK ends K u x := by
-- proof
  apply StatMech.Walls.gh4_mem_bondCompOf

/--
[gh4_bondCompOf_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_bondCompOf_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W} :
-- imply
  gh4_bondCompOf ends K u ⊆ K := by
-- proof
  apply StatMech.Walls.gh4_bondCompOf_subset ends K u

/--
[gh4_compMass_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_compMass_partition_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W} :
-- imply
  gc85b_pcount ends m V₁ V₂ = ∑ A ∈ m.powerset, gh4_compMass ends m V₁ V₂ u A := by
-- proof
  apply StatMech.Walls.gh4_compMass_partition ends m V₁ V₂ u

/--
[gh4_bondCompOf_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_bondCompOf_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W}
  {i : ι}
  {x : W}
-- given
  (hi : i ∈ gh4_bondCompOf ends K u)
  (hx : x ∈ ends i) :
-- imply
  connK ends K u x := by
-- proof
  apply StatMech.Walls.gh4_bondCompOf_conn ends K u hi hx

/--
[gh4_mark_in_comp_iff_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_mark_in_comp_iff_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u w : W} :
-- imply
  (∃ i ∈ gh4_bondCompOf ends K u, w ∈ ends i) ↔ (∃ i ∈ K, w ∈ ends i) ∧ connK ends K u w := by
-- proof
  apply StatMech.Walls.gh4_mark_in_comp_iff_conn ends K u w

/--
[gh4_drop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_drop_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {wgt diff : Finset ι → ℝ}
-- given
  (hwgt : ∀ A, 0 ≤ wgt A)
  (hdiff : ∀ A, 0 ≤ diff A) :
-- imply
  0 ≤ ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A := by
-- proof
  apply StatMech.Walls.gh4_drop_nonneg ends m V₁ V₂ u wgt diff hwgt hdiff

/--
[gh4_eq22_decomposition_of_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_eq22_decomposition_of_identity_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ V₁' V₂' : Finset W}
  {u u' : W}
  {wgtA diffA wgtB diffB : Finset ι → ℝ}
  {surv : ℝ}
-- given
  (β h : ℝ)
  (hwgtA : ∀ A, 0 ≤ wgtA A)
  (hdiffA : ∀ A, 0 ≤ diffA A)
  (hwgtB : ∀ B, 0 ≤ wgtB B)
  (hdiffB : ∀ B, 0 ≤ diffB B)
  (hident : eg_ursell3 G β h o x y = surv - 2 * (∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A) - 2 * (∑ B ∈ m.powerset, (gh4_compMass ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
-- imply
  gh3_eq22_decomposition G β h o x y := by
-- proof
  apply StatMech.Walls.gh4_eq22_decomposition_of_identity G β h o x y ends m V₁ V₂ V₁' V₂' u u' wgtA diffA wgtB diffB hwgtA hdiffA hwgtB hdiffB surv hident

/--
[gh4_compMass_le_pcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_compMass_le_pcount_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {A : Finset ι} :
-- imply
  gh4_compMass ends m V₁ V₂ u A ≤ gc85b_pcount ends m V₁ V₂ := by
-- proof
  apply StatMech.Walls.gh4_compMass_le_pcount ends m V₁ V₂ u A

/--
[gh4_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh4eq22.lean)
-/
@[path]
private lemma gh4_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh4_status


-- created on 2026-10-23
