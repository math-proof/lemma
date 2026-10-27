import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk010.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts20_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma vCounts20_checked_eq :
-- imply
  rawMomentVCounts 20 = generatedVCounts20 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts20_checked

/--
[qCounts20_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma qCounts20_checked_eq :
-- imply
  rawMomentQCounts 20 = generatedQCounts20 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts20_checked

/--
[stateCoefficients20_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma stateCoefficients20_checked_eq :
-- imply
  rawMomentStateCoefficientList 20 = generatedStateCoefficients20 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients20_checked

/--
[vCounts21_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma vCounts21_checked_eq :
-- imply
  rawMomentVCounts 21 = generatedVCounts21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts21_checked

/--
[qCounts21_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma qCounts21_checked_eq :
-- imply
  rawMomentQCounts 21 = generatedQCounts21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts21_checked

/--
[stateCoefficients21_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma stateCoefficients21_checked_eq :
-- imply
  rawMomentStateCoefficientList 21 = generatedStateCoefficients21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients21_checked

/--
[coefficientChunk10_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk010.lean)
-/
@[path]
private lemma coefficientChunk10_checked_eq :
-- imply
  rawMomentCoefficientSmallList 20 2 = generatedCoefficientChunk10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk10_checked


-- created on 2026-10-23
