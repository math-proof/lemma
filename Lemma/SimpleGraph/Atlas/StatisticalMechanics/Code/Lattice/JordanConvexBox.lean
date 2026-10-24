import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanConvexBox
open Set SimpleGraph StatMech StatMech.Lattice


/--
[jcb_upcross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_upcross_eq
  {a b : Site 2}
  {W : (hypercubicLattice 2).Walk a b}
  {c d : ℤ}
  {s : ℤ}
-- given
  (hac : a 1 = c)
  (hbd : b 1 = d)
  (hs1 : c < s)
  (hs2 : s ≤ d) :
-- imply
  ∃ i, 1 ≤ i ∧ i ≤ W.length ∧ (W.getVert i) 1 = s ∧ (W.getVert (i - 1)) 1 = s - 1 := by
-- proof
  apply StatMech.Lattice.jcb_upcross W hac hbd s hs1 hs2

/--
[jcb_vstep_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_vstep_col_eq
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hrow : u 1 - v 1 = 1 ∨ u 1 - v 1 = -1) :
-- imply
  u 0 = v 0 := by
-- proof
  apply StatMech.Lattice.jcb_vstep_col u v hadj hrow

/--
[jcb_rowMonotone_subpath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_rowMonotone_subpath_eq
  {a b : Site 2}
  {W : (hypercubicLattice 2).Walk a b}
  {c d : ℤ}
-- given
  (hac : a 1 = c)
  (hbd : b 1 = d)
  (_hcd : c ≤ d) :
-- imply
  ∃ Up : ℤ → ℕ, (∀ s, c < s → s ≤ d → 1 ≤ Up s ∧ Up s ≤ W.length ∧ (W.getVert (Up s)) 1 = s ∧ (W.getVert (Up s - 1)) 1 = s - 1) ∧ (∀ s t, c < s → s < t → t ≤ d → Up s < Up t) := by
-- proof
  apply StatMech.Lattice.jcb_rowMonotone_subpath W hac hbd _hcd

/--
[jcb_upcross_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_upcross_pair_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m m' c d : ℤ}
  {xB yT : Site 2}
  {s : ℤ}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hyT : yT ∈ rect m m' c d)
  (hxBc : xB 1 = c)
  (hyTd : yT 1 = d)
  (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
  (hs1 : c < s)
  (hs2 : s ≤ d) :
-- imply
  ∃ k : ℤ, m ≤ k ∧ k ≤ m' ∧ jsi_cell k s ∈ overlapComp ω m m' c d xB hxB ∧ jsi_cell k (s - 1) ∈ overlapComp ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.jcb_upcross_pair ω hxB hyT hxBc hyTd hcV s hs1 hs2

/--
[jcb_rowData_of_vCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_rowData_of_vCrossing_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m m' c d : ℤ}
  {xB yT : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hyT : yT ∈ rect m m' c d)
  (hxBc : xB 1 = c)
  (hyTd : yT 1 = d)
  (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩) :
-- imply
  ∃ col : ℤ → ℤ, (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧ (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧ (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) ∧ (∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ overlapComp ω m m' c d xB hxB) ∧ col (c - 1) = col c := by
-- proof
  apply StatMech.Lattice.jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV

/--
[jcb_separatingSide_of_vCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_separatingSide_of_vCrossing_eq
  {P : Set (Site 2)}
  {α β m m' c d : ℤ}
  {col : ℤ → ℤ}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β)
  (hcd : c ≤ d)
  (hlo : ∀ r, c ≤ r → r ≤ d → m ≤ col r)
  (hhi : ∀ r, c ≤ r → r ≤ d → col r ≤ m')
  (hon : ∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ P)
  (hcorner : ∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ P)
  (hc1 : col (c - 1) = col c)
  (hshift : ∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jcb_separatingSide_of_vCrossing hαm hm'β hcd col hlo hhi hon hcorner hc1 hshift

/--
[jcb_vsFix_arc_sides_of_vCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_vsFix_arc_sides_of_vCrossing_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β)
  (hres : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d), JcbColShift ω m m' c d xB hxB) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.jcb_vsFix_arc_sides_of_vCrossing ω hαm hm'β hres

/--
[jcb_colShift_of_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean)
-/
@[path]
private lemma jcb_colShift_of_shift_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m m' c d : ℤ}
  {xB yT : Site 2}
  {col : ℤ → ℤ}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hyT : yT ∈ rect m m' c d)
  (hxBc : xB 1 = c)
  (hyTd : yT 1 = d)
  (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
  (hcol : col = (jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV).choose)
  (hshift : ∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
-- imply
  JcbColShift ω m m' c d xB hxB := by
-- proof
  apply StatMech.Lattice.jcb_colShift_of_shift ω hxB hyT hxBc hyTd hcV col hcol hshift


-- created on 2026-10-23
