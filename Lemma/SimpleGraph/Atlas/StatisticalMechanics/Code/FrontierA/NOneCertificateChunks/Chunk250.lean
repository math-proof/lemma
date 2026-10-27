import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk250.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts500_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma vCounts500_checked_eq :
-- imply
  rawMomentVCounts 500 = generatedVCounts500 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts500_checked

/--
[qCounts500_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma qCounts500_checked_eq :
-- imply
  rawMomentQCounts 500 = generatedQCounts500 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts500_checked

/--
[stateCoefficients500_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma stateCoefficients500_checked_eq :
-- imply
  rawMomentStateCoefficientList 500 = generatedStateCoefficients500 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients500_checked

/--
[vCounts501_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma vCounts501_checked_eq :
-- imply
  rawMomentVCounts 501 = generatedVCounts501 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts501_checked

/--
[qCounts501_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma qCounts501_checked_eq :
-- imply
  rawMomentQCounts 501 = generatedQCounts501 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts501_checked

/--
[stateCoefficients501_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma stateCoefficients501_checked_eq :
-- imply
  rawMomentStateCoefficientList 501 = generatedStateCoefficients501 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients501_checked

/--
[coefficientChunk250_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean)
-/
@[path]
private lemma coefficientChunk250_checked_eq :
-- imply
  rawMomentCoefficientSmallList 500 2 = generatedCoefficientChunk250 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk250_checked


-- created on 2026-10-23
