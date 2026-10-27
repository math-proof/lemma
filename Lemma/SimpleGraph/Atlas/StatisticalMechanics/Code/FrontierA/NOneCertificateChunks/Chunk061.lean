import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk061.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts122_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma vCounts122_checked_eq :
-- imply
  rawMomentVCounts 122 = generatedVCounts122 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts122_checked

/--
[qCounts122_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma qCounts122_checked_eq :
-- imply
  rawMomentQCounts 122 = generatedQCounts122 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts122_checked

/--
[stateCoefficients122_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma stateCoefficients122_checked_eq :
-- imply
  rawMomentStateCoefficientList 122 = generatedStateCoefficients122 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients122_checked

/--
[vCounts123_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma vCounts123_checked_eq :
-- imply
  rawMomentVCounts 123 = generatedVCounts123 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts123_checked

/--
[qCounts123_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma qCounts123_checked_eq :
-- imply
  rawMomentQCounts 123 = generatedQCounts123 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts123_checked

/--
[stateCoefficients123_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma stateCoefficients123_checked_eq :
-- imply
  rawMomentStateCoefficientList 123 = generatedStateCoefficients123 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients123_checked

/--
[coefficientChunk61_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk061.lean)
-/
@[path]
private lemma coefficientChunk61_checked_eq :
-- imply
  rawMomentCoefficientSmallList 122 2 = generatedCoefficientChunk61 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk61_checked


-- created on 2026-10-23
