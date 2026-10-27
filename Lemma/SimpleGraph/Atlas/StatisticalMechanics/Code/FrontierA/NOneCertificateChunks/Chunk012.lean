import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk012.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts24_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma vCounts24_checked_eq :
-- imply
  rawMomentVCounts 24 = generatedVCounts24 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts24_checked

/--
[qCounts24_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma qCounts24_checked_eq :
-- imply
  rawMomentQCounts 24 = generatedQCounts24 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts24_checked

/--
[stateCoefficients24_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma stateCoefficients24_checked_eq :
-- imply
  rawMomentStateCoefficientList 24 = generatedStateCoefficients24 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients24_checked

/--
[vCounts25_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma vCounts25_checked_eq :
-- imply
  rawMomentVCounts 25 = generatedVCounts25 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts25_checked

/--
[qCounts25_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma qCounts25_checked_eq :
-- imply
  rawMomentQCounts 25 = generatedQCounts25 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts25_checked

/--
[stateCoefficients25_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma stateCoefficients25_checked_eq :
-- imply
  rawMomentStateCoefficientList 25 = generatedStateCoefficients25 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients25_checked

/--
[coefficientChunk12_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk012.lean)
-/
@[path]
private lemma coefficientChunk12_checked_eq :
-- imply
  rawMomentCoefficientSmallList 24 2 = generatedCoefficientChunk12 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk12_checked


-- created on 2026-10-23
