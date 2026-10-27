import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk192.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts384_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma vCounts384_checked_eq :
-- imply
  rawMomentVCounts 384 = generatedVCounts384 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts384_checked

/--
[qCounts384_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma qCounts384_checked_eq :
-- imply
  rawMomentQCounts 384 = generatedQCounts384 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts384_checked

/--
[stateCoefficients384_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma stateCoefficients384_checked_eq :
-- imply
  rawMomentStateCoefficientList 384 = generatedStateCoefficients384 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients384_checked

/--
[vCounts385_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma vCounts385_checked_eq :
-- imply
  rawMomentVCounts 385 = generatedVCounts385 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts385_checked

/--
[qCounts385_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma qCounts385_checked_eq :
-- imply
  rawMomentQCounts 385 = generatedQCounts385 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts385_checked

/--
[stateCoefficients385_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma stateCoefficients385_checked_eq :
-- imply
  rawMomentStateCoefficientList 385 = generatedStateCoefficients385 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients385_checked

/--
[coefficientChunk192_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk192.lean)
-/
@[path]
private lemma coefficientChunk192_checked_eq :
-- imply
  rawMomentCoefficientSmallList 384 2 = generatedCoefficientChunk192 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk192_checked


-- created on 2026-10-23
