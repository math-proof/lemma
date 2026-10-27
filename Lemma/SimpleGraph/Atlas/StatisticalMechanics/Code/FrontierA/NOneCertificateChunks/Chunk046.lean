import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk046.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts92_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma vCounts92_checked_eq :
-- imply
  rawMomentVCounts 92 = generatedVCounts92 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts92_checked

/--
[qCounts92_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma qCounts92_checked_eq :
-- imply
  rawMomentQCounts 92 = generatedQCounts92 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts92_checked

/--
[stateCoefficients92_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma stateCoefficients92_checked_eq :
-- imply
  rawMomentStateCoefficientList 92 = generatedStateCoefficients92 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients92_checked

/--
[vCounts93_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma vCounts93_checked_eq :
-- imply
  rawMomentVCounts 93 = generatedVCounts93 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts93_checked

/--
[qCounts93_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma qCounts93_checked_eq :
-- imply
  rawMomentQCounts 93 = generatedQCounts93 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts93_checked

/--
[stateCoefficients93_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma stateCoefficients93_checked_eq :
-- imply
  rawMomentStateCoefficientList 93 = generatedStateCoefficients93 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients93_checked

/--
[coefficientChunk46_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk046.lean)
-/
@[path]
private lemma coefficientChunk46_checked_eq :
-- imply
  rawMomentCoefficientSmallList 92 2 = generatedCoefficientChunk46 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk46_checked


-- created on 2026-10-23
