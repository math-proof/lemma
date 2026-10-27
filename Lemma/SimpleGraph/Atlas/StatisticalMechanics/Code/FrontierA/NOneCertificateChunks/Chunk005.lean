import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk005.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts10_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma vCounts10_checked_eq :
-- imply
  rawMomentVCounts 10 = generatedVCounts10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts10_checked

/--
[qCounts10_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma qCounts10_checked_eq :
-- imply
  rawMomentQCounts 10 = generatedQCounts10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts10_checked

/--
[stateCoefficients10_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma stateCoefficients10_checked_eq :
-- imply
  rawMomentStateCoefficientList 10 = generatedStateCoefficients10 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients10_checked

/--
[vCounts11_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma vCounts11_checked_eq :
-- imply
  rawMomentVCounts 11 = generatedVCounts11 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts11_checked

/--
[qCounts11_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma qCounts11_checked_eq :
-- imply
  rawMomentQCounts 11 = generatedQCounts11 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts11_checked

/--
[stateCoefficients11_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma stateCoefficients11_checked_eq :
-- imply
  rawMomentStateCoefficientList 11 = generatedStateCoefficients11 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients11_checked

/--
[coefficientChunk5_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean)
-/
@[path]
private lemma coefficientChunk5_checked_eq :
-- imply
  rawMomentCoefficientSmallList 10 2 = generatedCoefficientChunk5 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk5_checked


-- created on 2026-10-23
