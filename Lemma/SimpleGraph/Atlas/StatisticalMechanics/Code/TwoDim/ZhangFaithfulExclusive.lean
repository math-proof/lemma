import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
open MeasureTheory Set SimpleGraph StatMech StatMech.TwoDim


/--
[zfe_primalEmb_mid_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalEmb_mid_adj_eq
  {p q : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj p q) :
-- imply
  (hypercubicLattice 2).Adj (zfe_primalEmb p) (zfe_primalMid p q) := by
-- proof
  apply StatMech.TwoDim.zfe_primalEmb_mid_adj h

/--
[zfe_primalMid_emb_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalMid_emb_adj_eq
  {p q : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj p q) :
-- imply
  (hypercubicLattice 2).Adj (zfe_primalMid p q) (zfe_primalEmb q) := by
-- proof
  apply StatMech.TwoDim.zfe_primalMid_emb_adj h

/--
[zfe_faceEmb_mid_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_faceEmb_mid_adj_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  (hypercubicLattice 2).Adj (zfe_faceEmb f) (zfe_faceMid f g) := by
-- proof
  apply StatMech.TwoDim.zfe_faceEmb_mid_adj h

/--
[zfe_faceMid_emb_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_faceMid_emb_adj_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  (hypercubicLattice 2).Adj (zfe_faceMid f g) (zfe_faceEmb g) := by
-- proof
  apply StatMech.TwoDim.zfe_faceMid_emb_adj h

/--
[zfe_primalSubdiv_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalSubdiv_support_cases_eq
  {p q z : Site 2}
  {w : (hypercubicLattice 2).Walk p q}
-- given
  (hz : z ∈ (zfe_primalSubdiv w).support) :
-- imply
  (∃ u ∈ w.support, z = zfe_primalEmb u) ∨ ∃ u v, s(u, v) ∈ w.edges ∧ z = zfe_primalMid u v := by
-- proof
  apply StatMech.TwoDim.zfe_primalSubdiv_support_cases w hz

/--
[zfe_faceSubdiv_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_faceSubdiv_support_cases_eq
  {f g z : Site 2}
  {w : (hypercubicLattice 2).Walk f g}
-- given
  (hz : z ∈ (zfe_faceSubdiv w).support) :
-- imply
  (∃ u ∈ w.support, z = zfe_faceEmb u) ∨ ∃ u v, s(u, v) ∈ w.edges ∧ z = zfe_faceMid u v := by
-- proof
  apply StatMech.TwoDim.zfe_faceSubdiv_support_cases w hz

/--
[zfe_primalEmb_ne_faceEmb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalEmb_ne_faceEmb_eq
  {p f : Site 2} :
-- imply
  zfe_primalEmb p ≠ zfe_faceEmb f := by
-- proof
  apply StatMech.TwoDim.zfe_primalEmb_ne_faceEmb p f

/--
[zfe_primalEmb_ne_faceMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalEmb_ne_faceMid_eq
  {p f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  zfe_primalEmb p ≠ zfe_faceMid f g := by
-- proof
  apply StatMech.TwoDim.zfe_primalEmb_ne_faceMid hfg

/--
[zfe_primalMid_ne_faceEmb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_primalMid_ne_faceEmb_eq
  {p q f : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  zfe_primalMid p q ≠ zfe_faceEmb f := by
-- proof
  apply StatMech.TwoDim.zfe_primalMid_ne_faceEmb hpq

/--
[zfe_midpoint_sharedPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_midpoint_sharedPrimalEdge_eq
  {p q f g : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hmid : zfe_primalMid p q = zfe_faceMid f g) :
-- imply
  s(p, q) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.TwoDim.zfe_midpoint_sharedPrimalEdge hpq hfg hmid

/--
[zfe_subdiv_meeting_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_subdiv_meeting_edge_eq
  {a b c d z : Site 2}
  {H : (hypercubicLattice 2).Walk a b}
  {V : (hypercubicLattice 2).Walk c d}
-- given
  (hzH : z ∈ (zfe_primalSubdiv H).support)
  (hzV : z ∈ (zfe_faceSubdiv V).support) :
-- imply
  ∃ p q f g, s(p, q) ∈ H.edges ∧ s(f, g) ∈ V.edges ∧ s(p, q) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.TwoDim.zfe_subdiv_meeting_edge H V hzH hzV

/--
[zfe_liftWalk_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_liftWalk_edge_open_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {R : Set (Site 2)}
  {x y : R}
  {w : (openSubgraphInduce 2 omega R).Walk x y}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ (liftWalk omega R w).edges) :
-- imply
  omega e = true := by
-- proof
  apply StatMech.TwoDim.zfe_liftWalk_edge_open omega R w he

/--
[zfe_faithfulMatchedExclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_faithfulMatchedExclusive_eq
  {N : ℕ} :
-- imply
  zfk_FaithfulMatchedExclusive N := by
-- proof
  apply StatMech.TwoDim.zfe_faithfulMatchedExclusive N

/--
[zfe_percolationProbability_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_percolationProbability_zero_eq :
-- imply
  percolationProbability 2 (2⁻¹ : NNReal) StatMech.Universality.half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zfe_percolationProbability_zero

/--
[zfe_criticalProbability_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFaithfulExclusive.lean)
-/
@[path]
private lemma zfe_criticalProbability_eq_half_eq :
-- imply
  criticalProbability 2 = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.TwoDim.zfe_criticalProbability_eq_half


-- created on 2026-10-23
