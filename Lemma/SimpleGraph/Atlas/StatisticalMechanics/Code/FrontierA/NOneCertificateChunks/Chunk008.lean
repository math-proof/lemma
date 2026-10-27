import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk008.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts16_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma vCounts16_checked_eq :
-- imply
  rawMomentVCounts 16 = generatedVCounts16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts16_checked

/--
[qCounts16_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma qCounts16_checked_eq :
-- imply
  rawMomentQCounts 16 = generatedQCounts16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts16_checked

/--
[stateCoefficients16_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma stateCoefficients16_checked_eq :
-- imply
  rawMomentStateCoefficientList 16 = generatedStateCoefficients16 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients16_checked

/--
[vCounts17_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma vCounts17_checked_eq :
-- imply
  rawMomentVCounts 17 = generatedVCounts17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts17_checked

/--
[qCounts17_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma qCounts17_checked_eq :
-- imply
  rawMomentQCounts 17 = generatedQCounts17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts17_checked

/--
[stateCoefficients17_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma stateCoefficients17_checked_eq :
-- imply
  rawMomentStateCoefficientList 17 = generatedStateCoefficients17 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients17_checked

/--
[coefficientChunk8_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk008.lean)
-/
@[path]
private lemma coefficientChunk8_checked_eq :
-- imply
  rawMomentCoefficientSmallList 16 2 = generatedCoefficientChunk8 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk8_checked


-- created on 2026-10-23
