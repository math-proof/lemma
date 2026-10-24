import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk006
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts12_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma vCounts12_checked_eq :
-- imply
  rawMomentVCounts 12 = generatedVCounts12 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts12_checked

/--
[qCounts12_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma qCounts12_checked_eq :
-- imply
  rawMomentQCounts 12 = generatedQCounts12 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts12_checked

/--
[stateCoefficients12_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma stateCoefficients12_checked_eq :
-- imply
  rawMomentStateCoefficientList 12 = generatedStateCoefficients12 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients12_checked

/--
[vCounts13_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma vCounts13_checked_eq :
-- imply
  rawMomentVCounts 13 = generatedVCounts13 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts13_checked

/--
[qCounts13_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma qCounts13_checked_eq :
-- imply
  rawMomentQCounts 13 = generatedQCounts13 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts13_checked

/--
[stateCoefficients13_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma stateCoefficients13_checked_eq :
-- imply
  rawMomentStateCoefficientList 13 = generatedStateCoefficients13 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients13_checked

/--
[coefficientChunk6_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean)
-/
@[path]
private lemma coefficientChunk6_checked_eq :
-- imply
  rawMomentCoefficientSmallList 12 2 = generatedCoefficientChunk6 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk6_checked


-- created on 2026-10-23
