import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk025.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts50_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma vCounts50_checked_eq :
-- imply
  rawMomentVCounts 50 = generatedVCounts50 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts50_checked

/--
[qCounts50_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma qCounts50_checked_eq :
-- imply
  rawMomentQCounts 50 = generatedQCounts50 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts50_checked

/--
[stateCoefficients50_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma stateCoefficients50_checked_eq :
-- imply
  rawMomentStateCoefficientList 50 = generatedStateCoefficients50 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients50_checked

/--
[vCounts51_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma vCounts51_checked_eq :
-- imply
  rawMomentVCounts 51 = generatedVCounts51 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts51_checked

/--
[qCounts51_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma qCounts51_checked_eq :
-- imply
  rawMomentQCounts 51 = generatedQCounts51 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts51_checked

/--
[stateCoefficients51_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma stateCoefficients51_checked_eq :
-- imply
  rawMomentStateCoefficientList 51 = generatedStateCoefficients51 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients51_checked

/--
[coefficientChunk25_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean)
-/
@[path]
private lemma coefficientChunk25_checked_eq :
-- imply
  rawMomentCoefficientSmallList 50 2 = generatedCoefficientChunk25 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk25_checked


-- created on 2026-10-23
