import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk120.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts240_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma vCounts240_checked_eq :
-- imply
  rawMomentVCounts 240 = generatedVCounts240 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts240_checked

/--
[qCounts240_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma qCounts240_checked_eq :
-- imply
  rawMomentQCounts 240 = generatedQCounts240 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts240_checked

/--
[stateCoefficients240_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma stateCoefficients240_checked_eq :
-- imply
  rawMomentStateCoefficientList 240 = generatedStateCoefficients240 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients240_checked

/--
[vCounts241_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma vCounts241_checked_eq :
-- imply
  rawMomentVCounts 241 = generatedVCounts241 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts241_checked

/--
[qCounts241_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma qCounts241_checked_eq :
-- imply
  rawMomentQCounts 241 = generatedQCounts241 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts241_checked

/--
[stateCoefficients241_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma stateCoefficients241_checked_eq :
-- imply
  rawMomentStateCoefficientList 241 = generatedStateCoefficients241 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients241_checked

/--
[coefficientChunk120_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk120.lean)
-/
@[path]
private lemma coefficientChunk120_checked_eq :
-- imply
  rawMomentCoefficientSmallList 240 2 = generatedCoefficientChunk120 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk120_checked


-- created on 2026-10-23
