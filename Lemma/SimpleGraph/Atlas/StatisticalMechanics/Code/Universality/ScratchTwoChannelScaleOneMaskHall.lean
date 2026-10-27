import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part11
open StatMech StatMech.Universality


/--
[rlcScaleOnePairBlockFailure_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOnePairBlockFailure_card_eq :
-- imply
  Fintype.card RlcScaleOnePairBlockFailure = 3 := by
-- proof
  apply StatMech.Universality.rlcScaleOnePairBlockFailure_card

/--
[rlcScaleOneFiveBlockFailure_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFiveBlockFailure_card_eq :
-- imply
  Fintype.card RlcScaleOneFiveBlockFailure = 25 := by
-- proof
  apply StatMech.Universality.rlcScaleOneFiveBlockFailure_card

/--
[rlcScaleOneSectionAFailure_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionAFailure_card_eq :
-- imply
  Fintype.card RlcScaleOneSectionAFailure = 15000 := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionAFailure_card

/--
[rlcScaleOneSectionBFailure_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionBFailure_card_eq :
-- imply
  Fintype.card RlcScaleOneSectionBFailure = 3941 := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionBFailure_card

/--
[rlcScaleOneSectionCFailure_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionCFailure_card_eq :
-- imply
  Fintype.card RlcScaleOneSectionCFailure = 2002 := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionCFailure_card

/--
[rlcScaleOneSectionBList_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionBList_mem_eq
  {w : RlcScaleOneSectionB} :
-- imply
  w ∈ rlcScaleOneSectionBList ↔ rlcScaleOneSectionBAvoidsSelectedRoutes w = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionBList_mem w

/--
[rlcScaleOneSectionCList_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionCList_mem_eq
  {w : RlcScaleOneSectionC} :
-- imply
  w ∈ rlcScaleOneSectionCList ↔ rlcScaleOneSectionCAvoidsSelectedRoutes w = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionCList_mem w

/--
[rlcScaleOneSectionBList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionBList_length_eq :
-- imply
  rlcScaleOneSectionBList.length = 3941 := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionBList_length

/--
[rlcScaleOneSectionCList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneSectionCList_length_eq :
-- imply
  rlcScaleOneSectionCList.length = 2002 := by
-- proof
  apply StatMech.Universality.rlcScaleOneSectionCList_length

/--
[rlcScaleOneRouteClass_zero_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneRouteClass_zero_fixed_eq
  {omega : RlcScaleOneEdgeConfig}
-- given
  (h : rlcScaleOneRouteClass omega = 0) :
-- imply
  omega 6 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneRouteClass_zero_fixed omega h

/--
[rlcScaleOneRouteClass_one_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneRouteClass_one_fixed_eq
  {omega : RlcScaleOneEdgeConfig}
-- given
  (h : rlcScaleOneRouteClass omega = 1) :
-- imply
  omega 6 = true ∧ omega 11 = false ∧ omega 7 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneRouteClass_one_fixed omega h

/--
[rlcScaleOneRouteClass_two_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneRouteClass_two_fixed_eq
  {omega : RlcScaleOneEdgeConfig}
-- given
  (h : rlcScaleOneRouteClass omega = 2) :
-- imply
  omega 6 = true ∧ omega 11 = true ∧ omega 7 = false ∧ omega 9 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneRouteClass_two_fixed omega h

/--
[rlcScaleOneRouteClass_three_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneRouteClass_three_fixed_eq
  {omega : RlcScaleOneEdgeConfig}
-- given
  (h : rlcScaleOneRouteClass omega = 3) :
-- imply
  omega 6 = true ∧ (omega 11 = true ∨ omega 7 = true) ∧ (omega 9 = true ∨ omega 7 = true) := by
-- proof
  apply StatMech.Universality.rlcScaleOneRouteClass_three_fixed omega h

/--
[rlcScaleOneBoolCubeToBitVec_getLsb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneBoolCubeToBitVec_getLsb_eq
  {n : Nat}
  {bits : Fin n → Bool}
  {i : Fin n} :
-- imply
  (rlcScaleOneBoolCubeToBitVec n bits).getLsb i = bits i := by
-- proof
  apply StatMech.Universality.rlcScaleOneBoolCubeToBitVec_getLsb bits i

/--
[rlcScaleOneCodeA_ne_codeB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeA_ne_codeB_eq
  {a : Fin 14 → Bool}
  {b : Fin 12 → Bool} :
-- imply
  rlcScaleOneCodeA a ≠ rlcScaleOneCodeB b := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeA_ne_codeB a b

/--
[rlcScaleOneCodeA_ne_codeC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeA_ne_codeC_eq
  {a : Fin 14 → Bool}
  {c : Fin 11 → Bool} :
-- imply
  rlcScaleOneCodeA a ≠ rlcScaleOneCodeC c := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeA_ne_codeC a c

/--
[rlcScaleOneCodeA_ne_codeD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeA_ne_codeD_eq
  {a : Fin 14 → Bool}
  {d : Fin 12 → Bool} :
-- imply
  rlcScaleOneCodeA a ≠ rlcScaleOneCodeD d := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeA_ne_codeD a d

/--
[rlcScaleOneCodeB_ne_codeC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeB_ne_codeC_eq
  {b : Fin 12 → Bool}
  {c : Fin 11 → Bool} :
-- imply
  rlcScaleOneCodeB b ≠ rlcScaleOneCodeC c := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeB_ne_codeC b c

/--
[rlcScaleOneCodeB_ne_codeD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeB_ne_codeD_eq
  {b d : Fin 12 → Bool} :
-- imply
  rlcScaleOneCodeB b ≠ rlcScaleOneCodeD d := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeB_ne_codeD b d

/--
[rlcScaleOneCodeC_ne_codeD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneCodeC_ne_codeD_eq
  {c : Fin 11 → Bool}
  {d : Fin 12 → Bool} :
-- imply
  rlcScaleOneCodeC c ≠ rlcScaleOneCodeD d := by
-- proof
  apply StatMech.Universality.rlcScaleOneCodeC_ne_codeD c d

/--
[rlcScaleOneTaggedTarget_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneTaggedTarget_success_eq
  {rho : RlcScaleOneRoutedFailure} :
-- imply
  rlcScaleOneFourRouteSuccess (rlcScaleOneTaggedTarget rho) = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneTaggedTarget_success rho

/--
[rlcScaleOneFailure_route_not_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_route_not_open_eq
  {rho : RlcScaleOneConnectorFailure}
  {mask : Nat}
-- given
  (hmask : mask ∈ rlcScaleOneRouteMasks) :
-- imply
  ¬RlcScaleOneRouteOpen rho.1 mask := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_route_not_open rho hmask

/--
[rlcScaleOne_exists_closed_edge_of_route_not_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOne_exists_closed_edge_of_route_not_open_eq
  {omega : RlcScaleOneEdgeConfig}
  {mask : Nat}
-- given
  (h : ¬RlcScaleOneRouteOpen omega mask) :
-- imply
  ∃ i : Fin 16, mask.testBit i ∧ omega i = false := by
-- proof
  apply StatMech.Universality.rlcScaleOne_exists_closed_edge_of_route_not_open omega mask h

/--
[rlcScaleOneFailure_closed_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed_edge_eq
  {rho : RlcScaleOneConnectorFailure}
  {mask : Nat}
-- given
  (hmask : mask ∈ rlcScaleOneRouteMasks) :
-- imply
  ∃ i : Fin 16, mask.testBit i ∧ rho.1 i = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed_edge rho hmask

/--
[rlcScaleOneMask384_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask384_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 384 i) :
-- imply
  i = 7 ∨ i = 8 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask384_support i h

/--
[rlcScaleOneMask19_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask19_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 19 i) :
-- imply
  i = 0 ∨ i = 1 ∨ i = 4 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask19_support i h

/--
[rlcScaleOneMask7168_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask7168_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 7168 i) :
-- imply
  i = 10 ∨ i = 11 ∨ i = 12 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask7168_support i h

/--
[rlcScaleOneMask28_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask28_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 28 i) :
-- imply
  i = 2 ∨ i = 3 ∨ i = 4 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask28_support i h

/--
[rlcScaleOneMask50176_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask50176_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 50176 i) :
-- imply
  i = 10 ∨ i = 14 ∨ i = 15 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask50176_support i h

/--
[rlcScaleOneMask8960_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask8960_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 8960 i) :
-- imply
  i = 8 ∨ i = 9 ∨ i = 13 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask8960_support i h

/--
[rlcScaleOneMask13312_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask13312_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 13312 i) :
-- imply
  i = 10 ∨ i = 12 ∨ i = 13 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask13312_support i h

/--
[rlcScaleOneMask8800_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask8800_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 8800 i) :
-- imply
  i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 13 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask8800_support i h

/--
[rlcScaleOneMask56_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask56_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 56 i) :
-- imply
  i = 3 ∨ i = 4 ∨ i = 5 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask56_support i h

/--
[rlcScaleOneMask344_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask344_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 344 i) :
-- imply
  i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask344_support i h

/--
[rlcScaleOneMask224_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask224_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 224 i) :
-- imply
  i = 5 ∨ i = 6 ∨ i = 7 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask224_support i h

/--
[rlcScaleOneMask196_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask196_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 196 i) :
-- imply
  i = 2 ∨ i = 6 ∨ i = 7 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask196_support i h

/--
[rlcScaleOneMask2816_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask2816_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 2816 i) :
-- imply
  i = 8 ∨ i = 9 ∨ i = 11 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask2816_support i h

/--
[rlcScaleOneMask2628_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask2628_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 2628 i) :
-- imply
  i = 2 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask2628_support i h

/--
[rlcScaleOneMask2656_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneMask2656_support_eq
  {i : Fin 16}
-- given
  (h : Nat.testBit 2656 i) :
-- imply
  i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by
-- proof
  apply StatMech.Universality.rlcScaleOneMask2656_support i h

/--
[rlcScaleOneFailure_closed384](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed384_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  rho.1 7 = false ∨ rho.1 8 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed384 rho

/--
[rlcScaleOneFailure_closed19](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed19_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 0 = false ∨ rho.1 1 = false) ∨ rho.1 4 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed19 rho

/--
[rlcScaleOneFailure_closed7168](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed7168_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 10 = false ∨ rho.1 11 = false) ∨ rho.1 12 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed7168 rho

/--
[rlcScaleOneFailure_closed28](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed28_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 2 = false ∨ rho.1 3 = false) ∨ rho.1 4 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed28 rho

/--
[rlcScaleOneFailure_closed50176](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed50176_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 10 = false ∨ rho.1 14 = false) ∨ rho.1 15 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed50176 rho

/--
[rlcScaleOneFailure_closed8960](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed8960_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 13 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed8960 rho

/--
[rlcScaleOneFailure_closed13312](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed13312_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 10 = false ∨ rho.1 12 = false) ∨ rho.1 13 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed13312 rho

/--
[rlcScaleOneFailure_closed8800](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed8800_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨ rho.1 13 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed8800 rho

/--
[rlcScaleOneFailure_closed56](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed56_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 5 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed56 rho

/--
[rlcScaleOneFailure_closed344](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed344_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  ((rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 6 = false) ∨ rho.1 8 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed344 rho

/--
[rlcScaleOneFailure_closed224](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed224_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed224 rho

/--
[rlcScaleOneFailure_closed196](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed196_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed196 rho

/--
[rlcScaleOneFailure_closed2816](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed2816_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 11 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed2816 rho

/--
[rlcScaleOneFailure_closed2628](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed2628_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  ((rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨ rho.1 11 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed2628 rho

/--
[rlcScaleOneFailure_closed2656](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_closed2656_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨ rho.1 11 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_closed2656 rho

/--
[rlcScaleOneFailure_fiberA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_fiberA_eq
  {rho : RlcScaleOneConnectorFailure}
-- given
  (_hclass : rlcScaleOneRouteClass rho.1 = 0) :
-- imply
  rlcScaleOneSectionAAvoidsSelectedRoutes (rlcScaleOneRestrictA rho.1) = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_fiberA rho _hclass

/--
[rlcScaleOneBool_false_of_true_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneBool_false_of_true_of_false_eq
  {b : Bool}
-- given
  (htrue : b = true)
  (hfalse : b = false) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rlcScaleOneBool_false_of_true_of_false htrue hfalse

/--
[rlcScaleOneFailure_fiberB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_fiberB_eq
  {rho : RlcScaleOneConnectorFailure}
-- given
  (hclass : rlcScaleOneRouteClass rho.1 = 1) :
-- imply
  rlcScaleOneSectionBAvoidsSelectedRoutes (rlcScaleOneRestrictB rho.1) = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_fiberB rho hclass

/--
[rlcScaleOneFailure_fiberC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_fiberC_eq
  {rho : RlcScaleOneConnectorFailure}
-- given
  (hclass : rlcScaleOneRouteClass rho.1 = 2) :
-- imply
  rlcScaleOneSectionCAvoidsSelectedRoutes (rlcScaleOneRestrictC rho.1) = true := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_fiberC rho hclass

/--
[rlcScaleOneFailure_fiberD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailure_fiberD_eq
  {rho : RlcScaleOneConnectorFailure}
-- given
  (hclass : rlcScaleOneRouteClass rho.1 = 3) :
-- imply
  rho.1 2 = false ∧ rho.1 5 = false ∧ rho.1 6 = true ∧ rho.1 8 = false := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailure_fiberD rho hclass

/--
[rlcScaleOneFailureClassify_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFailureClassify_config_eq
  {rho : RlcScaleOneConnectorFailure} :
-- imply
  rlcScaleOneRoutedFailureConfig (rlcScaleOneFailureClassify rho) = rho.1 := by
-- proof
  apply StatMech.Universality.rlcScaleOneFailureClassify_config rho

/--
[rlcScaleOneTaggedTarget_connectorSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneTaggedTarget_connectorSuccess_eq
  {rho : RlcScaleOneRoutedFailure} :
-- imply
  RlcScaleOneConnectorSuccess (rlcScaleOneTaggedTarget rho) := by
-- proof
  apply StatMech.Universality.rlcScaleOneTaggedTarget_connectorSuccess rho

/--
[rlcScaleOneFiberA_reservedBit_not_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean)
-/
@[path]
private lemma rlcScaleOneFiberA_reservedBit_not_pointwise_eq :
-- imply
  ∃ rho sigma : RlcScaleOneFiberA, rho.1 7 ≠ sigma.1 7 := by
-- proof
  apply StatMech.Universality.rlcScaleOneFiberA_reservedBit_not_pointwise


-- created on 2026-10-23
