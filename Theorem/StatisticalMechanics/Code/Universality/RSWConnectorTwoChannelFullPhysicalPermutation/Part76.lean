/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part75
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_staticCutFailure_unrepairableTerminalProduct
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hfailure : ¬∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y) :
    RlcTwoChannelFullPhysicalUnrepairableTerminalProductObstruction
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega := by
    intro hgood
    exact hfailure
      (rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent
        gamma gamma' A hAright hAleft hgood)
  obtain ⟨z, x, y, u, right, flipLeft, c, hcycle, hx, hy,
      hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder,
      hflipLeftRank, hfirst, hrankRealized, hglobalMin⟩ :=
    rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure
      gamma gamma' hfaith omega hno
  obtain ⟨ur, vr, ul, vl, qRepairR, qRepairL, qr, ql, rr, rl,
      hurv, hulv, hdecR, hdecL, hlenR, hlenL,
      hnotR, hnotL, hbadR, hbadL,
      hclassR, hclassL, hproduct⟩ :=
    rlc_twoChannelFullPhysical_unrepairableTerminalProductClassification
      hfaith hno hnoGood c hx hy hxPath hyPath
  have hordered :=
    rlc_twoChannelFullPhysical_orderedWallAlternative_of_product
      hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath
        hxOrder hyOrder hfirst qr ql hproduct
  have hexact :=
    rlc_twoChannelFullPhysical_exactOrderedWallAlternative_of_product
      hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath
        hxOrder hyOrder hfirst qr ql hproduct
  exact ⟨z, x, y, u, right, flipLeft, c, hx, hy, ur, vr, ul, vl,
    qRepairR, qRepairL, qr, ql, rr, rl, hurv, hulv, hcycle,
    hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank,
    hfirst, hrankRealized, hglobalMin,
    hdecR, hdecL, hlenR, hlenL,
    hnotR, hnotL, hbadR, hbadL, hclassR, hclassL,
    hproduct, hordered, hexact⟩


theorem
    rlc_twoChannelFullPhysical_noPair_unrepairableTerminalProduct
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
    RlcTwoChannelFullPhysicalUnrepairableTerminalProductObstruction
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  apply rlc_twoChannelFullPhysical_staticCutFailure_unrepairableTerminalProduct
    gamma gamma' hfaith A hAright hAleft
  exact rlc_twoChannelFullPhysical_staticCutTargetFailure_of_noPair
    gamma gamma' A B hBright hBleft hnoPair


theorem
    rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_product_or_shorter
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y ur vr ul vl f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl))
    (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega ur vr)
    (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega ul vl)
    (hfgCycle : s(f, g) ∈ c.edges)
    (hfgBad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(ur, vr) ∨
      (∃ (u' v' : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk y u')
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vr)
        (huv : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'),
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' u' v' ∧
          rr.reverse =
            (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
              gamma gamma' omega)).append (.cons huv r) ∧
          (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
          r.length < rr.length ∧
          r.length + rl.length < rr.length + rl.length ∧
          RlcTwoChannelFullPhysicalLeftArcClassifiedBad
            gamma gamma' omega u' v' ∧
          RlcTwoChannelFullPhysicalWallTerminalProductClassification
            gamma gamma' omega (vr := vr) (vl := v') qr q ∧
          RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
            gamma gamma' omega (vr := vr) (vl := v') qr q) ∨
      s(f, g) = s(ul, vl) ∨
      ∃ (u' v' : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk x u')
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vl)
        (huv : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'),
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' u' v' ∧
          rl.reverse =
            (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
              gamma gamma' omega)).append (.cons huv r) ∧
          (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
          r.length < rl.length ∧
          rr.length + r.length < rr.length + rl.length ∧
          RlcTwoChannelFullPhysicalRightArcClassifiedBad
            gamma gamma' omega u' v' ∧
          RlcTwoChannelFullPhysicalWallTerminalProductClassification
            gamma gamma' omega (vr := v') (vl := vl) q ql ∧
          RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
            gamma gamma' omega (vr := v') (vl := vl) q ql := by
  rcases
      rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_exact_or_reverseFirstExit
        c hx hy qr rr ql rl hurv hulv hdecR hdecL hfgCycle hfgBad with
      hbadR | hrr | hbadL | hrl
  · exact Or.inl hbadR
  · right; left
    obtain ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder,
        hlength⟩ := hrr
    have hclassNew :=
      rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix
        hno hnoGood hyPath q huv hbad
    have hproduct :=
      rlc_twoChannelFullPhysical_wallTerminalProductClassification
        hfaith qr q hxPath hyPath hclassR hclassNew
    have hlocalized :=
      rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product
        hproduct
    exact ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder, hlength,
      by omega, hclassNew, hproduct, hlocalized⟩
  · right; right; left
    exact hbadL
  · right; right; right
    obtain ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder,
        hlength⟩ := hrl
    have hclassNew :=
      rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix
        hno hnoGood hxPath q huv hbad
    have hproduct :=
      rlc_twoChannelFullPhysical_wallTerminalProductClassification
        hfaith q ql hxPath hyPath hclassNew hclassL
    have hlocalized :=
      rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product
        hproduct
    exact ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder, hlength,
      by omega, hclassNew, hproduct, hlocalized⟩


theorem
    rlc_twoChannelFullPhysical_noPair_BChanging_terminal_or_strictSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u x y ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).append (.cons hulv rl))
    (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ur vr)
    (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ul vl) :
    ∃ f g : Site 2,
      rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
      (s(f, g) = s(ur, vr) ∨
        (∃ (u' v' : Site 2)
          (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)).Walk y u')
          (r : (faceBoundaryGraph
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))).Walk v' vr)
          (huv : (faceBoundaryGraph
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))).Adj u' v'),
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' u' v' ∧
            rr.reverse =
              (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
                gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A))).append (.cons huv r) ∧
            (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
            r.length < rr.length ∧
            r.length + rl.length < rr.length + rl.length ∧
            RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) u' v' ∧
            RlcTwoChannelFullPhysicalWallTerminalProductClassification
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) (vr := vr) (vl := v') qr q ∧
            RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) (vr := vr) (vl := v') qr q) ∨
        s(f, g) = s(ul, vl) ∨
        ∃ (u' v' : Site 2)
          (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)).Walk x u')
          (r : (faceBoundaryGraph
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))).Walk v' vl)
          (huv : (faceBoundaryGraph
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))).Adj u' v'),
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' u' v' ∧
            rl.reverse =
              (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
                gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A))).append (.cons huv r) ∧
            (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
            r.length < rl.length ∧
            rr.length + r.length < rr.length + rl.length ∧
            RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) u' v' ∧
            RlcTwoChannelFullPhysicalWallTerminalProductClassification
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) (vr := v') (vl := vl) q ql ∧
            RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) (vr := v') (vl := vl) q ql) := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega :=
    rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
  obtain ⟨f, g, hfgCycle, hfgCross, hfgBad⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_BChanging_exactNoncarrier_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
        c hx hy hxPath hyPath
  refine ⟨f, g, hfgCross, ?_⟩
  exact rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_product_or_shorter
    hfaith hno hnoGood c hx hy hxPath hyPath qr rr ql rl hurv hulv
      hdecR hdecL hclassR hclassL hfgCycle hfgBad


theorem rlc_twoChannelFullPhysical_suffixPair_strongInduction
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (P : ∀ {a b c d : Site 2},
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b →
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d →
      Prop)
    (hstep : ∀ {a b c d : Site 2}
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d),
      (∀ {a' b' c' d' : Site 2}
        (rr' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b')
        (rl' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'),
        rr'.length + rl'.length < rr.length + rl.length → P rr' rl') →
      P rr rl) :
    ∀ {a b c d : Site 2}
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d),
      P rr rl := by
  intro a b c d rr rl
  generalize hm : rr.length + rl.length = m
  induction m using Nat.strong_induction_on generalizing a b c d rr rl with
  | h m ih =>
      apply hstep rr rl
      intro a' b' c' d' rr' rl' hlt
      exact ih (rr'.length + rl'.length) (by omega) rr' rl' rfl


theorem rlc_twoChannelFullPhysical_candidateSuffix_lexStrongInduction
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (P : Nat → ∀ {a b c d : Site 2},
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b →
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d →
      Prop)
    (hstep : ∀ (k : Nat) {a b c d : Site 2}
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d),
      (∀ (k' : Nat), k' < k → ∀ {a' b' c' d' : Site 2}
        (rr' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b')
        (rl' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'),
        P k' rr' rl') →
      (∀ {a' b' c' d' : Site 2}
        (rr' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b')
        (rl' : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'),
        rr'.length + rl'.length < rr.length + rl.length →
          P k rr' rl') →
      P k rr rl) :
    ∀ (k : Nat) {a b c d : Site 2}
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d),
      P k rr rl := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ihK =>
      intro a b c d rr rl
      generalize hm : rr.length + rl.length = m
      induction m using Nat.strong_induction_on generalizing a b c d rr rl with
      | h m ihM =>
          apply hstep k rr rl
          · intro k' hk a' b' c' d' rr' rl'
            exact ihK k' hk rr' rl'
          · intro a' b' c' d' rr' rl' hlt
            exact ihM (rr'.length + rl'.length) (by omega) rr' rl' rfl


end
end StatMech.Universality
