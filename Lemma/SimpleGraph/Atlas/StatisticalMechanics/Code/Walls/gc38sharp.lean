import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc38sharp
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc38_comp_sources_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_comp_sources_even_eq
  [DecidableEq ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) :
-- imply
  Even (#((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K))) := by
-- proof
  apply StatMech.Walls.gc38_comp_sources_even ends K hnd u

/--
[gc38_comp_source_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_comp_source_count_eq
  [DecidableEq ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {u : W}
-- given
  (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
  (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) :
-- imply
  #((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K)) = (if RandomCurrent.connK ends K u o then 1 else 0) + (if RandomCurrent.connK ends K u x then 1 else 0) + (if RandomCurrent.connK ends K u y then 1 else 0) + (if RandomCurrent.connK ends K u g then 1 else 0) := by
-- proof
  apply StatMech.Walls.gc38_comp_source_count ends K hdist hsrc u

/--
[gc38_disconn_triple_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_disconn_triple_identity_eq
  [DecidableEq ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
  (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) :
-- imply
  (if ¬ RandomCurrent.connK ends K x y then (1 : ℝ) else 0) + (if ¬ RandomCurrent.connK ends K y g then 1 else 0) + (if ¬ RandomCurrent.connK ends K x g then 1 else 0) = 2 * (if ¬ (RandomCurrent.connK ends K o x ∧ RandomCurrent.connK ends K o y ∧ RandomCurrent.connK ends K o g) then 1 else 0) := by
-- proof
  apply StatMech.Walls.gc38_disconn_triple_identity ends K hnd hdist hsrc

/--
[gc38_sourcePairAllConnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_sourcePairAllConnSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ gc38_sourcePairAllConnSum G β J A o x y g := by
-- proof
  apply StatMech.Walls.gc38_sourcePairAllConnSum_nonneg G β J hβ hJ A o x y g

/--
[gc38_allConnSum_eq_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_allConnSum_eq_edgecopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {o x y g : V} :
-- imply
  gc38_sourcePairAllConnSum G β J A o x y g = ∑' m : ↥G.edgeFinset → ℕ, (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Walls.gc38_allConnSum_eq_edgecopy G β J A o x y g

/--
[gc38_perSuperposition_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_perSuperposition_assembly_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {o x y g : V}
-- given
  (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
-- imply
  ((∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ x y then 1 else 0)) + (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ y g then 1 else 0)) + (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ x g then 1 else 0))) = 2 * (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)) - 2 * (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)) := by
-- proof
  apply StatMech.Walls.gc38_perSuperposition_assembly G β J m hdist

/--
[gc38_summable_edgecopy_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_summable_edgecopy_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {o x y g : V}
-- given
  (hJnn : ∀ e, 0 ≤ J e)
  (hβ : 0 ≤ β) :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)) * weight G β J (ofEdgeFun G m)) := by
-- proof
  apply StatMech.Walls.gc38_summable_edgecopy_allConn G β J hJnn hβ A o x y g

/--
[gc38_disconnSum_triple_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_disconnSum_triple_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
-- imply
  sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x y + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ y g + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x g = 2 * sourcePairSum G β J ({o, x, y, g} : Finset V) ∅ - 2 * gc38_sourcePairAllConnSum G β J ({o, x, y, g} : Finset V) o x y g := by
-- proof
  apply StatMech.Walls.gc38_disconnSum_triple_eq G β J hβ hJ hdist

/--
[gc38_Z0sq_U4_eq_neg_two_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_Z0sq_U4_eq_neg_two_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y = -2 * gc38_sourcePairAllConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none := by
-- proof
  apply StatMech.Walls.gc38_Z0sq_U4_eq_neg_two_allConn G β h hβ hh o x y hox hoy hxy

/--
[gc38_U4_nonpos_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_U4_nonpos_unconditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy

/--
[gc38_U4_nonpos_replaces_connRep_hypothesis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_U4_nonpos_replaces_connRep_hypothesis_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc38_U4_nonpos_replaces_connRep_hypothesis G β h hβ hh o x y hox hoy hxy

/--
[gc38_ursell3_nonpos_of_sharpResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_ursell3_nonpos_of_sharpResidue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hres : gc38_SharpGHSResidue G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc38_ursell3_nonpos_of_sharpResidue G β h o x y hres

/--
[gc38_sharp_gap_is_two_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_sharp_gap_is_two_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 ∧ 0 ≤ gc37_triple G β h o x y ∧ (gc38_SharpGHSResidue G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0) := by
-- proof
  apply StatMech.Walls.gc38_sharp_gap_is_two_triple G β h hβ hh o x y hox hoy hxy

/--
[gc38_sharpResidue_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean)
-/
@[path]
private lemma gc38_sharpResidue_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  gc38_SharpGHSResidue G β 0 o x y := by
-- proof
  apply StatMech.Walls.gc38_sharpResidue_at_zero G β o x y


-- created on 2026-10-23
