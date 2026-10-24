import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk022
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts44_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma vCounts44_checked_eq :
-- imply
  rawMomentVCounts 44 = generatedVCounts44 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts44_checked

/--
[qCounts44_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma qCounts44_checked_eq :
-- imply
  rawMomentQCounts 44 = generatedQCounts44 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts44_checked

/--
[stateCoefficients44_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma stateCoefficients44_checked_eq :
-- imply
  rawMomentStateCoefficientList 44 = generatedStateCoefficients44 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients44_checked

/--
[vCounts45_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma vCounts45_checked_eq :
-- imply
  rawMomentVCounts 45 = generatedVCounts45 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts45_checked

/--
[qCounts45_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma qCounts45_checked_eq :
-- imply
  rawMomentQCounts 45 = generatedQCounts45 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts45_checked

/--
[stateCoefficients45_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma stateCoefficients45_checked_eq :
-- imply
  rawMomentStateCoefficientList 45 = generatedStateCoefficients45 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients45_checked

/--
[coefficientChunk22_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk022.lean)
-/
@[path]
private lemma coefficientChunk22_checked_eq :
-- imply
  rawMomentCoefficientSmallList 44 2 = generatedCoefficientChunk22 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk22_checked


-- created on 2026-10-23
