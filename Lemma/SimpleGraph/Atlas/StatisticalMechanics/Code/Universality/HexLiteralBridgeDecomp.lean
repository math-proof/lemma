import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralBridgeDecomp
open StatMech StatMech.Universality


/--
[hexHW_literalSplit_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_literalSplit_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hexHW_literalSplit a h0) := by
-- proof
  apply StatMech.Universality.hexHW_literalSplit_injective a h0

/--
[hexHW_literal_bridge_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_literal_bridge_decomp_eq
  {a : ℂ}
  {d : {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts}}
-- given
  (h0 : ℤ) :
-- imply
  let cp := hexW2_cutPos h0 d.1 let b := hexW2_prefixBridge h0 d.1 d.2.2 d.1 = (hexHW_literalSplit a h0 d).1.turns ++ (hexHW_literalSplit a h0 d).2.turns ∧ b.content = (hexHW_literalSplit a h0 d).1.turns ∧ 0 < b.width ∧ hexWall3_ReachesWidth a h0 b.width b.content ∧ (HexWalk.ofTurns a h0 b.content).IsLegalSAW ∧ (HexWalk.ofTurns (hexDropMid a h0 d.1 cp) (h0 + (d.1.take cp).sum) (hexHW_literalSplit a h0 d).2.turns).IsLegalSAW ∧ (∀ k ≤ d.1.length, hexW2_partialDisp h0 d.1 k ≤ hexW2_partialDisp h0 d.1 cp) ∧ (∀ k, k < cp → hexW2_partialDisp h0 d.1 k < hexW2_partialDisp h0 d.1 cp) := by
-- proof
  apply StatMech.Universality.hexHW_literal_bridge_decomp a h0 d

/--
[hexHW_literal_bridge_decomp_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralBridgeDecomp.lean)
-/
@[path]
private lemma hexHW_literal_bridge_decomp_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hexHW_literalSplit a h0) ∧ ∀ d : {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts}, let cp := hexW2_cutPos h0 d.1 let b := hexW2_prefixBridge h0 d.1 d.2.2 d.1 = (hexHW_literalSplit a h0 d).1.turns ++ (hexHW_literalSplit a h0 d).2.turns ∧ b.content = (hexHW_literalSplit a h0 d).1.turns ∧ 0 < b.width ∧ hexWall3_ReachesWidth a h0 b.width b.content ∧ (HexWalk.ofTurns a h0 b.content).IsLegalSAW ∧ (HexWalk.ofTurns (hexDropMid a h0 d.1 cp) (h0 + (d.1.take cp).sum) (hexHW_literalSplit a h0 d).2.turns).IsLegalSAW ∧ (∀ k ≤ d.1.length, hexW2_partialDisp h0 d.1 k ≤ hexW2_partialDisp h0 d.1 cp) ∧ (∀ k, k < cp → hexW2_partialDisp h0 d.1 k < hexW2_partialDisp h0 d.1 cp) := by
-- proof
  apply StatMech.Universality.hexHW_literal_bridge_decomp_injective a h0


-- created on 2026-10-23
