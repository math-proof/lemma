import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexAlignedPairedBranchTotalC
open StatMech StatMech.FrontierD


/--
[localCIndicator_exchange_complementary_boundary_aligned_masks_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedPairedBranchTotalC.lean)
-/
@[path]
private lemma localCIndicator_exchange_complementary_boundary_aligned_masks_exact_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ vertexParity select0 select1 : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  exchangedLocalAlignedMaskCIndicator select0 select1 (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q + exchangedLocalAlignedMaskCIndicator (!select0) (!select1) (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q = 2 * (localCIndicator p + localCIndicator q) + 2 * (if (select0 != select1) && (pairingP != pairingQ) && (vertexParity != sideVertical d) then 2 else 0) := by
-- proof
  apply StatMech.FrontierD.localCIndicator_exchange_complementary_boundary_aligned_masks_exact p q pairingP pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[alignedMaskedComplementaryTargets_aggregateTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedPairedBranchTotalC.lean)
-/
@[path]
private lemma alignedMaskedComplementaryTargets_aggregateTotalC_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (select0 select1 : T.Vertex -> Bool)
  (hbond : AlignedMaskedBondConsistent homega heta hdegree select0 select1)
  (hbondComplement : AlignedMaskedBondConsistent homega heta hdegree (fun v => !select0 v) (fun v => !select1 v)) :
-- imply
  2 * (sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta) <= (sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree select0 select1 false) + sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree select0 select1 true)) + (sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree (fun v => !select0 v) (fun v => !select1 v) false) + sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree (fun v => !select0 v) (fun v => !select1 v) true)) := by
-- proof
  apply StatMech.FrontierD.alignedMaskedComplementaryTargets_aggregateTotalC homega heta hdegree select0 select1 hbond hbondComplement


-- created on 2026-10-23
