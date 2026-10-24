import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk016
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts32_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma vCounts32_checked_eq :
-- imply
  rawMomentVCounts 32 = generatedVCounts32 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts32_checked

/--
[qCounts32_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma qCounts32_checked_eq :
-- imply
  rawMomentQCounts 32 = generatedQCounts32 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts32_checked

/--
[stateCoefficients32_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma stateCoefficients32_checked_eq :
-- imply
  rawMomentStateCoefficientList 32 = generatedStateCoefficients32 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients32_checked

/--
[vCounts33_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma vCounts33_checked_eq :
-- imply
  rawMomentVCounts 33 = generatedVCounts33 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts33_checked

/--
[qCounts33_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma qCounts33_checked_eq :
-- imply
  rawMomentQCounts 33 = generatedQCounts33 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts33_checked

/--
[stateCoefficients33_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma stateCoefficients33_checked_eq :
-- imply
  rawMomentStateCoefficientList 33 = generatedStateCoefficients33 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients33_checked

/--
[coefficientChunk16_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean)
-/
@[path]
private lemma coefficientChunk16_checked_eq :
-- imply
  rawMomentCoefficientSmallList 32 2 = generatedCoefficientChunk16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk16_checked


-- created on 2026-10-23
