import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ArcMonotonise
open Set SimpleGraph StatMech StatMech.Lattice


/--
[amo_connectedWithin_of_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_connectedWithin_of_mem_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {a b : (S : Set (Site 2))}
  {W : (openSubgraphInduce 2 ω S).Walk a b}
  {z : (S : Set (Site 2))}
-- given
  (hz : z ∈ W.support) :
-- imply
  ConnectedWithin 2 ω S a z := by
-- proof
  apply StatMech.Lattice.amo_connectedWithin_of_mem_support ω S W hz

/--
[amo_overlapComp_visits_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_overlapComp_visits_row_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m m' c d : ℤ}
  {xB yT : Site 2}
  {r : ℤ}
-- given
  (hxB : xB ∈ rect m m' c d)
  (hyT : yT ∈ rect m m' c d)
  (hxBc : xB 1 = c)
  (hyTd : yT 1 = d)
  (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
  (hcr : c ≤ r)
  (hrd : r ≤ d) :
-- imply
  ∃ z : Site 2, z ∈ overlapComp ω m m' c d xB hxB ∧ z 1 = r ∧ m ≤ z 0 ∧ z 0 ≤ m' := by
-- proof
  apply StatMech.Lattice.amo_overlapComp_visits_row ω hxB hyT hxBc hyTd hcV r hcr hrd

/--
[amo_rowCell_of_vCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_rowCell_of_vCrossing_eq
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
  ∃ col : ℤ → ℤ, (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧ (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧ (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) := by
-- proof
  apply StatMech.Lattice.amo_rowCell_of_vCrossing ω hxB hyT hxBc hyTd hcV

/--
[amo_overlapComp_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_overlapComp_allClosed_eq
  {m m' c d : ℤ}
  {xB : Site 2}
-- given
  (hxB : xB ∈ rect m m' c d) :
-- imply
  overlapComp (fun _ => false) m m' c d xB hxB = {xB} := by
-- proof
  apply StatMech.Lattice.amo_overlapComp_allClosed m m' c d xB hxB

/--
[amo_singleton_no_monotoneArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_singleton_no_monotoneArc_eq
  {m m' c d : ℤ}
  {pt : Site 2}
  {A : JsiMonotoneArc ({pt} : Set (Site 2)) m m' c d}
-- given
  (hcd : c < d) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.amo_singleton_no_monotoneArc pt hcd A

/--
[amo_hasMonotoneArc_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean)
-/
@[path]
private lemma amo_hasMonotoneArc_false_eq
  {m m' c d : ℤ}
-- given
  (hmm' : m ≤ m')
  (hcd : c < d) :
-- imply
  ¬ JsiHasMonotoneArc (fun _ => false) m m' c d := by
-- proof
  apply StatMech.Lattice.amo_hasMonotoneArc_false hmm' hcd


-- created on 2026-10-23
