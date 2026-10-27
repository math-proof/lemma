import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk111.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts222_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma vCounts222_checked_eq :
-- imply
  rawMomentVCounts 222 = generatedVCounts222 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts222_checked

/--
[qCounts222_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma qCounts222_checked_eq :
-- imply
  rawMomentQCounts 222 = generatedQCounts222 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts222_checked

/--
[stateCoefficients222_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma stateCoefficients222_checked_eq :
-- imply
  rawMomentStateCoefficientList 222 = generatedStateCoefficients222 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients222_checked

/--
[vCounts223_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma vCounts223_checked_eq :
-- imply
  rawMomentVCounts 223 = generatedVCounts223 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts223_checked

/--
[qCounts223_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma qCounts223_checked_eq :
-- imply
  rawMomentQCounts 223 = generatedQCounts223 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts223_checked

/--
[stateCoefficients223_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma stateCoefficients223_checked_eq :
-- imply
  rawMomentStateCoefficientList 223 = generatedStateCoefficients223 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients223_checked

/--
[coefficientChunk111_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean)
-/
@[path]
private lemma coefficientChunk111_checked_eq :
-- imply
  rawMomentCoefficientSmallList 222 2 = generatedCoefficientChunk111 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk111_checked


-- created on 2026-10-23
