import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk060
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts120_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma vCounts120_checked_eq :
-- imply
  rawMomentVCounts 120 = generatedVCounts120 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts120_checked

/--
[qCounts120_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma qCounts120_checked_eq :
-- imply
  rawMomentQCounts 120 = generatedQCounts120 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts120_checked

/--
[stateCoefficients120_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma stateCoefficients120_checked_eq :
-- imply
  rawMomentStateCoefficientList 120 = generatedStateCoefficients120 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients120_checked

/--
[vCounts121_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma vCounts121_checked_eq :
-- imply
  rawMomentVCounts 121 = generatedVCounts121 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts121_checked

/--
[qCounts121_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma qCounts121_checked_eq :
-- imply
  rawMomentQCounts 121 = generatedQCounts121 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts121_checked

/--
[stateCoefficients121_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma stateCoefficients121_checked_eq :
-- imply
  rawMomentStateCoefficientList 121 = generatedStateCoefficients121 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients121_checked

/--
[coefficientChunk60_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean)
-/
@[path]
private lemma coefficientChunk60_checked_eq :
-- imply
  rawMomentCoefficientSmallList 120 2 = generatedCoefficientChunk60 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk60_checked


-- created on 2026-10-23
