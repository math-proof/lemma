import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk042.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts84_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma vCounts84_checked_eq :
-- imply
  rawMomentVCounts 84 = generatedVCounts84 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts84_checked

/--
[qCounts84_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma qCounts84_checked_eq :
-- imply
  rawMomentQCounts 84 = generatedQCounts84 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts84_checked

/--
[stateCoefficients84_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma stateCoefficients84_checked_eq :
-- imply
  rawMomentStateCoefficientList 84 = generatedStateCoefficients84 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients84_checked

/--
[vCounts85_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma vCounts85_checked_eq :
-- imply
  rawMomentVCounts 85 = generatedVCounts85 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts85_checked

/--
[qCounts85_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma qCounts85_checked_eq :
-- imply
  rawMomentQCounts 85 = generatedQCounts85 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts85_checked

/--
[stateCoefficients85_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma stateCoefficients85_checked_eq :
-- imply
  rawMomentStateCoefficientList 85 = generatedStateCoefficients85 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients85_checked

/--
[coefficientChunk42_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean)
-/
@[path]
private lemma coefficientChunk42_checked_eq :
-- imply
  rawMomentCoefficientSmallList 84 2 = generatedCoefficientChunk42 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk42_checked


-- created on 2026-10-23
