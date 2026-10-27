import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk240.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts480_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma vCounts480_checked_eq :
-- imply
  rawMomentVCounts 480 = generatedVCounts480 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts480_checked

/--
[qCounts480_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma qCounts480_checked_eq :
-- imply
  rawMomentQCounts 480 = generatedQCounts480 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts480_checked

/--
[stateCoefficients480_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma stateCoefficients480_checked_eq :
-- imply
  rawMomentStateCoefficientList 480 = generatedStateCoefficients480 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients480_checked

/--
[vCounts481_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma vCounts481_checked_eq :
-- imply
  rawMomentVCounts 481 = generatedVCounts481 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts481_checked

/--
[qCounts481_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma qCounts481_checked_eq :
-- imply
  rawMomentQCounts 481 = generatedQCounts481 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts481_checked

/--
[stateCoefficients481_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma stateCoefficients481_checked_eq :
-- imply
  rawMomentStateCoefficientList 481 = generatedStateCoefficients481 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients481_checked

/--
[coefficientChunk240_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk240.lean)
-/
@[path]
private lemma coefficientChunk240_checked_eq :
-- imply
  rawMomentCoefficientSmallList 480 2 = generatedCoefficientChunk240 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk240_checked


-- created on 2026-10-23
