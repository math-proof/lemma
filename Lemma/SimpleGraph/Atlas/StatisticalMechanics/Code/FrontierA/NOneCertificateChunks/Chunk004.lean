import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk004.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts8_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma vCounts8_checked_eq :
-- imply
  rawMomentVCounts 8 = generatedVCounts8 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts8_checked

/--
[qCounts8_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma qCounts8_checked_eq :
-- imply
  rawMomentQCounts 8 = generatedQCounts8 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts8_checked

/--
[stateCoefficients8_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma stateCoefficients8_checked_eq :
-- imply
  rawMomentStateCoefficientList 8 = generatedStateCoefficients8 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients8_checked

/--
[vCounts9_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma vCounts9_checked_eq :
-- imply
  rawMomentVCounts 9 = generatedVCounts9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts9_checked

/--
[qCounts9_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma qCounts9_checked_eq :
-- imply
  rawMomentQCounts 9 = generatedQCounts9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts9_checked

/--
[stateCoefficients9_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma stateCoefficients9_checked_eq :
-- imply
  rawMomentStateCoefficientList 9 = generatedStateCoefficients9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients9_checked

/--
[coefficientChunk4_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean)
-/
@[path]
private lemma coefficientChunk4_checked_eq :
-- imply
  rawMomentCoefficientSmallList 8 2 = generatedCoefficientChunk4 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk4_checked


-- created on 2026-10-23
