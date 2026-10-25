/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoTauAdjustedState_trueDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      doubledAlignedBlackDart homega heta hdegree false x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [sixVertexDegreeTwoTauAdjustedState, if_pos heq]
    have h := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    simpa [retie, heq] using h
  · rw [sixVertexDegreeTwoTauAdjustedState, if_neg heq]
    have h := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simpa [retie, heq] using h

@[simp] theorem sixVertexDegreeTwoTauAdjustedState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x).1 = x.1 := by
  change (if (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ then x
    else doubledAlignedBranchSwap x).1 = x.1
  split <;> simp

theorem sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = x := by
  rw [sixVertexDegreeTwoTauAdjustedState, if_pos heq]

theorem sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hne : ¬(orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x =
      doubledAlignedBranchSwap x := by
  rw [sixVertexDegreeTwoTauAdjustedState, if_neg hne]

@[simp] theorem sixVertexDegreeTwoTauAdjustedState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = x := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
      homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq]
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
      homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree (doubledAlignedBranchSwap x) heq',
      doubledAlignedBranchSwap_self]

theorem sixVertexDegreeTwoTauAdjustedState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
      homega heta hdegree (doubledAlignedBranchSwap x) heq',
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq]
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
      homega heta hdegree (doubledAlignedBranchSwap x) heq',
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      doubledAlignedBranchSwap_self]

theorem sixVertexDegreeTwoCanonicalExpandedInputState_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedInputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq _ _ _ _ heq']
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedInputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree _ heq']

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedOutputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq _ _ _ _ heq']
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedOutputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree _ heq']


end
end StatMech.FrontierD
