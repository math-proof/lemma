import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk020.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts40_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma vCounts40_checked_eq :
-- imply
  rawMomentVCounts 40 = generatedVCounts40 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts40_checked

/--
[qCounts40_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma qCounts40_checked_eq :
-- imply
  rawMomentQCounts 40 = generatedQCounts40 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts40_checked

/--
[stateCoefficients40_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma stateCoefficients40_checked_eq :
-- imply
  rawMomentStateCoefficientList 40 = generatedStateCoefficients40 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients40_checked

/--
[vCounts41_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma vCounts41_checked_eq :
-- imply
  rawMomentVCounts 41 = generatedVCounts41 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts41_checked

/--
[qCounts41_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma qCounts41_checked_eq :
-- imply
  rawMomentQCounts 41 = generatedQCounts41 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts41_checked

/--
[stateCoefficients41_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma stateCoefficients41_checked_eq :
-- imply
  rawMomentStateCoefficientList 41 = generatedStateCoefficients41 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients41_checked

/--
[coefficientChunk20_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk020.lean)
-/
@[path]
private lemma coefficientChunk20_checked_eq :
-- imply
  rawMomentCoefficientSmallList 40 2 = generatedCoefficientChunk20 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk20_checked


-- created on 2026-10-23
