import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc37hdom
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc37_ursell3_eq_U4_add_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_ursell3_eq_U4_add_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc37_ursell3_eq_U4_add_triple G β h o x y

/--
[gc37_onePt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_onePt_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation G β h (fun s => spin s x) := by
-- proof
  apply StatMech.Walls.gc37_onePt_nonneg G β h hβ hh x

/--
[gc37_triple_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_triple_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc37_triple_nonneg G β h hβ hh o x y

/--
[gc37_sourcePairSum_conn_add_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_sourcePairSum_conn_add_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {u v : V} :
-- imply
  sourcePairSum G β J A B = gc37_sourcePairConnSum G β J A B u v + sourcePairDisconnSum G β J A B u v := by
-- proof
  apply StatMech.Walls.gc37_sourcePairSum_conn_add_disconn G β J A B u v

/--
[gc37_sourcePairConnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_sourcePairConnSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ gc37_sourcePairConnSum G β J A B u v := by
-- proof
  apply StatMech.Walls.gc37_sourcePairConnSum_nonneg G β J hβ hJ A B u v

/--
[gc37_Z0cubed_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_Z0cubed_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y = csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb)) * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb)) * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
-- proof
  apply StatMech.Walls.gc37_Z0cubed_triple G β h o x y

/--
[gc37_Z0sq_U4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_Z0sq_U4_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y = (gc15_Z0 G β h) * csG G β h (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) - csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb)) * csG G β h (({x, y} : Finset V).map someEmb) - csG G β h (({o, x} : Finset V).map someEmb) * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb)) - csG G β h (({o, y} : Finset V).map someEmb) * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb)) := by
-- proof
  apply StatMech.Walls.gc37_Z0sq_U4 G β h o x y hox hoy hxy

/--
[gc37_U4_nonpos_of_connRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_U4_nonpos_of_connRep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hrep : gc37_U4a_connRep G β h o x y) :
-- imply
  gc37_U4 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc37_U4_nonpos_of_connRep G β h hβ hh o x y hrep

/--
[gc37_twoReplica_U4_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_twoReplica_U4_insufficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ 0 < a + 2 * b := by
-- proof
  apply StatMech.Walls.gc37_twoReplica_U4_insufficient G

/--
[gc37_ursell3_nonpos_iff_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_ursell3_nonpos_iff_sharp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y := by
-- proof
  apply StatMech.Walls.gc37_ursell3_nonpos_iff_sharp G β h o x y

/--
[gc37_ursell3_nonpos_of_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_ursell3_nonpos_of_sharp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hsharp : gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc37_ursell3_nonpos_of_sharp G β h o x y hsharp

/--
[gc37_U4_eq_neg_two_triple_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean)
-/
@[path]
private lemma gc37_U4_eq_neg_two_triple_at_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  gc37_U4 G β 0 o x y = -2 * gc37_triple G β 0 o x y := by
-- proof
  apply StatMech.Walls.gc37_U4_eq_neg_two_triple_at_zero G β o x y


-- created on 2026-10-23
