import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue.Part3
open StatMech StatMech.Onsager


/--
[ons_portEdge_eq_positiveHorizontal_of_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_portEdge_eq_positiveHorizontal_of_horizontal_eq
  {L : Nat}
  {d : ons_Dart L}
-- given
  (hdir : d.2 = 0 ∨ d.2 = 2) :
-- imply
  ons_portEdge L d = ons_portEdge L (ons_positiveHorizontalSource d, 0) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_positiveHorizontal_of_horizontal d hdir

/--
[ons_portEdge_eq_positiveVertical_of_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_portEdge_eq_positiveVertical_of_vertical_eq
  {L : Nat}
  {d : ons_Dart L}
-- given
  (hdir : d.2 = 1 ∨ d.2 = 3) :
-- imply
  ons_portEdge L d = ons_portEdge L (ons_positiveVerticalSource d, 1) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_positiveVertical_of_vertical d hdir

/--
[ons_portEdge_eq_of_dartHorizontal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_portEdge_eq_of_dartHorizontal_ne_zero_eq
  {L : Nat}
  {d : ons_Dart L}
  {z : ZMod L × ZMod L}
-- given
  (h : IntegralSquareTorusCycle.dartHorizontal d z ≠ 0) :
-- imply
  ons_portEdge L d = ons_portEdge L (z, 0) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_of_dartHorizontal_ne_zero d z h

/--
[ons_portEdge_eq_of_dartVertical_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_portEdge_eq_of_dartVertical_ne_zero_eq
  {L : Nat}
  {d : ons_Dart L}
  {z : ZMod L × ZMod L}
-- given
  (h : IntegralSquareTorusCycle.dartVertical d z ≠ 0) :
-- imply
  ons_portEdge L d = ons_portEdge L (z, 1) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_of_dartVertical_ne_zero d z h

/--
[IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ofDarts_horizontal_eq_zero_of_not_mem_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hnot : ons_portEdge L (z, 0) ∉ ons_dartEdgeSet v) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z = 0 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem v hvalid z hnot

/--
[IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ofDarts_vertical_eq_zero_of_not_mem_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hnot : ons_portEdge L (z, 1) ∉ ons_dartEdgeSet v) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z = 0 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem v hvalid z hnot

/--
[ons_residueOutgoingCoeff_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueOutgoingCoeff_divergence_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L} :
-- imply
  ∑ mu : Fin 4, ons_residueOutgoingCoeff C p z mu = 0 := by
-- proof
  apply StatMech.Onsager.ons_residueOutgoingCoeff_divergence C p z

/--
[ons_residueOutgoingCoeff_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueOutgoingCoeff_dartRev_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {d : ons_Dart L} :
-- imply
  ons_residueOutgoingCoeff C p (ons_dartRev L d).1 (ons_dartRev L d).2 = -ons_residueOutgoingCoeff C p d.1 d.2 := by
-- proof
  apply StatMech.Onsager.ons_residueOutgoingCoeff_dartRev C p d

/--
[ons_residueOutgoingCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueOutgoingCoeff_eq_zero_of_not_mem_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [NeZero p]
  {v : Fin n → ons_Dart L}
  {z : ZMod L × ZMod L}
  {mu : Fin 4}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
  (hnot : ons_portEdge L (z, mu) ∉ ons_dartEdgeSet v) :
-- imply
  ons_residueOutgoingCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p z mu = 0 := by
-- proof
  apply StatMech.Onsager.ons_residueOutgoingCoeff_eq_zero_of_not_mem v hvalid hx hy z mu hnot

/--
[ons_residueLoopCoeff_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueLoopCoeff_pred_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [NeZero p]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
-- imply
  ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v k = ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v (k - 1) := by
-- proof
  apply StatMech.Onsager.ons_residueLoopCoeff_pred v hvalid hsite hnu hx hy k

/--
[ons_residueLoopCoeff_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueLoopCoeff_constant_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [NeZero p]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
-- imply
  ∀ k, ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v k = ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v 0 := by
-- proof
  apply StatMech.Onsager.ons_residueLoopCoeff_constant v hvalid hsite hnu hx hy

/--
[IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ofDarts_horizontal_eq_single_of_portEdge_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hport : ons_portEdge L (v k) = ons_portEdge L (z, 0)) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z = IntegralSquareTorusCycle.dartHorizontal (v k) z := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge v hvalid hsite hnu k z hport

/--
[IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ofDarts_vertical_eq_single_of_portEdge_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hport : ons_portEdge L (v k) = ons_portEdge L (z, 1)) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z = IntegralSquareTorusCycle.dartVertical (v k) z := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge v hvalid hsite hnu k z hport

/--
[ons_residueOutgoingCoeff_ne_zero_on_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueOutgoingCoeff_ne_zero_on_loop_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [Fact (1 < p)]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
-- imply
  ons_residueOutgoingCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p (v k).1 (v k).2 ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_residueOutgoingCoeff_ne_zero_on_loop v hvalid hsite hnu hx hy k

/--
[ons_residueLoopCoeff_zero_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_residueLoopCoeff_zero_ne_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [Fact (1 < p)]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
-- imply
  ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v 0 ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_residueLoopCoeff_zero_ne v hvalid hsite hnu hx hy

/--
[IntegralSquareTorusCycle.residueHorizontalCoeff_eq_mul_horizontal_of_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma residueHorizontalCoeff_eq_mul_horizontal_of_loop_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [NeZero p]
  {v : Fin n → ons_Dart L}
  {c : Int}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hc : ∀ k, ons_residueOutgoingCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p (v k).1 (v k).2 = c) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).residueHorizontalCoeff p z = c * (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.residueHorizontalCoeff_eq_mul_horizontal_of_loop v hvalid hsite hnu hx c hc z

/--
[IntegralSquareTorusCycle.residueVerticalCoeff_eq_mul_vertical_of_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma residueVerticalCoeff_eq_mul_vertical_of_loop_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [NeZero p]
  {v : Fin n → ons_Dart L}
  {c : Int}
  {z : ZMod L × ZMod L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
  (hc : ∀ k, ons_residueOutgoingCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p (v k).1 (v k).2 = c) :
-- imply
  (IntegralSquareTorusCycle.ofDarts v hvalid).residueVerticalCoeff p z = c * (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.residueVerticalCoeff_eq_mul_vertical_of_loop v hvalid hsite hnu hy c hc z

/--
[IntegralSquareTorusCycle.sum_dartHorizontal_eq_dirExponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma sum_dartHorizontal_eq_dirExponentX_eq
  {L : Nat}
  [NeZero L]
  {d : ons_Dart L} :
-- imply
  (∑ z : ZMod L × ZMod L, IntegralSquareTorusCycle.dartHorizontal d z) = ons_dirExponentX d.2 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.sum_dartHorizontal_eq_dirExponentX d

/--
[IntegralSquareTorusCycle.sum_dartVertical_eq_dirExponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma sum_dartVertical_eq_dirExponentY_eq
  {L : Nat}
  [NeZero L]
  {d : ons_Dart L} :
-- imply
  (∑ z : ZMod L × ZMod L, IntegralSquareTorusCycle.dartVertical d z) = ons_dirExponentY d.2 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.sum_dartVertical_eq_dirExponentY d

/--
[IntegralSquareTorusCycle.sum_ofDarts_horizontal_eq_dirExponentX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma sum_ofDarts_horizontal_eq_dirExponentX_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  (∑ z, (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z) = ∑ k, ons_dirExponentX (v k).2 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.sum_ofDarts_horizontal_eq_dirExponentX v hvalid

/--
[IntegralSquareTorusCycle.sum_ofDarts_vertical_eq_dirExponentY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma sum_ofDarts_vertical_eq_dirExponentY_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  (∑ z, (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z) = ∑ k, ons_dirExponentY (v k).2 := by
-- proof
  apply StatMech.Onsager.IntegralSquareTorusCycle.sum_ofDarts_vertical_eq_dirExponentY v hvalid

/--
[ons_simpleLoop_displacement_eq_zero_of_common_flux_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_simpleLoop_displacement_eq_zero_of_common_flux_divisor_eq
  {L n p : Nat}
  [Fact (2 < L)]
  [NeZero n]
  [Fact (1 < p)]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hx : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
  (hy : (p : Int) ∣ (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
-- imply
  (∑ k, ons_dirExponentX (v k).2) = 0 ∧ (∑ k, ons_dirExponentY (v k).2) = 0 := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_displacement_eq_zero_of_common_flux_divisor v hvalid hsite hnu hx hy

/--
[ons_simpleLoop_winding_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean)
-/
@[path]
private lemma ons_simpleLoop_winding_primitive_eq
  {L n : Nat}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : Int}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : Int) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : Int) * my)
  (hnonzero : (mx, my) ≠ (0, 0)) :
-- imply
  ∃ a b : Int, a * mx + b * my = 1 := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_winding_primitive v hvalid hsite hnu mx my hmx hmy hnonzero


-- created on 2026-10-23
