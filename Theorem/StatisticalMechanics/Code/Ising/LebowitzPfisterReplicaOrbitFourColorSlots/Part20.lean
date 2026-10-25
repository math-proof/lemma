/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part20
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrientedFourColorSlotState_injective
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaOrientedFourColorSlotState G sites A B q) := by
  rintro ⟨m, ⟨a, ⟨⟨P, L⟩, ⟨Sa, Sb⟩⟩⟩⟩
    ⟨n, ⟨b, ⟨⟨Q, M⟩, ⟨Ta, Tb⟩⟩⟩⟩ hstate
  have halloc := congrArg
    (fun s : LPReplicaOrbitFourColorSlotState G sites q => s.allocation)
    hstate
  change (fun e => (L e).1) = (fun e => (M e).1) at halloc
  have hmnVal : m.1 = n.1 :=
    lpReplicaProfile_eq_of_orbitLabel_allocation_eq
      G sites q m.1 n.1 m.2 n.2 L M halloc
  have hmn : m = n := Subtype.ext hmnVal
  subst n
  have hLM : L = M := by
    funext e
    apply Subtype.ext
    exact congrFun halloc e
  subst M
  have htag :
      lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
          (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1 =
        lpReplicaOrbitCollisionSplitTag G sites m.1 b.1 Q.1
          (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1 := by
    exact lpReplicaOrbitFourColorSlotStateOfTag_injective
      G sites q m.1 m.2 L hstate
  have habVal : a.1 = b.1 := by
    calc
      a.1 = lpReplicaTaggedOriginProfile G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
            (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1) false :=
        (lpReplicaOrbitCollisionSplitTag_originProfile_false
          G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2
            Sa.1 Sb.1).symm
      _ = lpReplicaTaggedOriginProfile G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 b.1 Q.1
            (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1) false :=
        congrArg (fun tag =>
          lpReplicaTaggedOriginProfile G sites m.1 tag false) htag
      _ = b.1 := lpReplicaOrbitCollisionSplitTag_originProfile_false
        G sites m.1 b.1 Q.1 (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1
  have hab : a = b := Subtype.ext habVal
  subst b
  have hPQVal : P.1 = Q.1 := by
    calc
      P.1 = lpReplicaRowCopies G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
            (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1) false :=
        (lpReplicaOrbitCollisionSplitTag_rowCopies_false
          G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2
            Sa.1 Sb.1).symm
      _ = lpReplicaRowCopies G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 Q.1
            (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1) false :=
        congrArg (fun tag => lpReplicaRowCopies G sites m.1 tag false) htag
      _ = Q.1 := lpReplicaOrbitCollisionSplitTag_rowCopies_false
        G sites m.1 a.1 Q.1 (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1
  have hPQ : P = Q := Subtype.ext hPQVal
  subst Q
  have hcurr : (Sa.1, Sb.1) = (Ta.1, Tb.1) :=
    lpReplicaOrbitCollisionSplitTag_currentSubsets_injective
      G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2 htag
  have hSa : Sa = Ta := Subtype.ext (congrArg Prod.fst hcurr)
  have hSb : Sb = Tb := Subtype.ext (congrArg Prod.snd hcurr)
  subst Ta
  subst Tb
  rfl


theorem lpReplicaOrientedFourColorSlotState_leftPattern
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    LPReplicaOrbitFourColorSlotLeftPattern G sites q A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
      (lpReplicaOrientedFourColorSlotState G sites A B q z) := by
  exact lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
    G sites q z.1.1 z.1.2 z.2.2.1.2
    (lpReplicaOrientedFourColorTag G sites A B q z) A
    (B.map lpReplicaCurrentReflect.toEmbedding)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
    (lpReplicaOrientedFourColorTag_leftPattern G sites A B q z)


end
end StatMech.Ising
