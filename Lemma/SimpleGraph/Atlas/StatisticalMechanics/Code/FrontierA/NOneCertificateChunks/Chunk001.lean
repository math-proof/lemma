import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk001.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts2_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma vCounts2_checked_eq :
-- imply
  rawMomentVCounts 2 = generatedVCounts2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts2_checked

/--
[qCounts2_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma qCounts2_checked_eq :
-- imply
  rawMomentQCounts 2 = generatedQCounts2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts2_checked

/--
[stateCoefficients2_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma stateCoefficients2_checked_eq :
-- imply
  rawMomentStateCoefficientList 2 = generatedStateCoefficients2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients2_checked

/--
[vCounts3_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma vCounts3_checked_eq :
-- imply
  rawMomentVCounts 3 = generatedVCounts3 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts3_checked

/--
[qCounts3_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma qCounts3_checked_eq :
-- imply
  rawMomentQCounts 3 = generatedQCounts3 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts3_checked

/--
[stateCoefficients3_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma stateCoefficients3_checked_eq :
-- imply
  rawMomentStateCoefficientList 3 = generatedStateCoefficients3 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients3_checked

/--
[coefficientChunk1_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk001.lean)
-/
@[path]
private lemma coefficientChunk1_checked_eq :
-- imply
  rawMomentCoefficientSmallList 2 2 = generatedCoefficientChunk1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk1_checked


-- created on 2026-10-23
