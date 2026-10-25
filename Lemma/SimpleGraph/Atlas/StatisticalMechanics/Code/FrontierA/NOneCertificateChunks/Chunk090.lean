import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk090.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts180_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma vCounts180_checked_eq :
-- imply
  rawMomentVCounts 180 = generatedVCounts180 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts180_checked

/--
[qCounts180_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma qCounts180_checked_eq :
-- imply
  rawMomentQCounts 180 = generatedQCounts180 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts180_checked

/--
[stateCoefficients180_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma stateCoefficients180_checked_eq :
-- imply
  rawMomentStateCoefficientList 180 = generatedStateCoefficients180 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients180_checked

/--
[vCounts181_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma vCounts181_checked_eq :
-- imply
  rawMomentVCounts 181 = generatedVCounts181 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts181_checked

/--
[qCounts181_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma qCounts181_checked_eq :
-- imply
  rawMomentQCounts 181 = generatedQCounts181 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts181_checked

/--
[stateCoefficients181_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma stateCoefficients181_checked_eq :
-- imply
  rawMomentStateCoefficientList 181 = generatedStateCoefficients181 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients181_checked

/--
[coefficientChunk90_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean)
-/
@[path]
private lemma coefficientChunk90_checked_eq :
-- imply
  rawMomentCoefficientSmallList 180 2 = generatedCoefficientChunk90 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk90_checked


-- created on 2026-10-23
