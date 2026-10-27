import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk003.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts6_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma vCounts6_checked_eq :
-- imply
  rawMomentVCounts 6 = generatedVCounts6 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts6_checked

/--
[qCounts6_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma qCounts6_checked_eq :
-- imply
  rawMomentQCounts 6 = generatedQCounts6 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts6_checked

/--
[stateCoefficients6_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma stateCoefficients6_checked_eq :
-- imply
  rawMomentStateCoefficientList 6 = generatedStateCoefficients6 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients6_checked

/--
[vCounts7_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma vCounts7_checked_eq :
-- imply
  rawMomentVCounts 7 = generatedVCounts7 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts7_checked

/--
[qCounts7_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma qCounts7_checked_eq :
-- imply
  rawMomentQCounts 7 = generatedQCounts7 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts7_checked

/--
[stateCoefficients7_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma stateCoefficients7_checked_eq :
-- imply
  rawMomentStateCoefficientList 7 = generatedStateCoefficients7 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients7_checked

/--
[coefficientChunk3_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk003.lean)
-/
@[path]
private lemma coefficientChunk3_checked_eq :
-- imply
  rawMomentCoefficientSmallList 6 2 = generatedCoefficientChunk3 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk3_checked


-- created on 2026-10-23
