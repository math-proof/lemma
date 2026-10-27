import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk180.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts360_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma vCounts360_checked_eq :
-- imply
  rawMomentVCounts 360 = generatedVCounts360 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts360_checked

/--
[qCounts360_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma qCounts360_checked_eq :
-- imply
  rawMomentQCounts 360 = generatedQCounts360 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts360_checked

/--
[stateCoefficients360_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma stateCoefficients360_checked_eq :
-- imply
  rawMomentStateCoefficientList 360 = generatedStateCoefficients360 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients360_checked

/--
[vCounts361_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma vCounts361_checked_eq :
-- imply
  rawMomentVCounts 361 = generatedVCounts361 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts361_checked

/--
[qCounts361_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma qCounts361_checked_eq :
-- imply
  rawMomentQCounts 361 = generatedQCounts361 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts361_checked

/--
[stateCoefficients361_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma stateCoefficients361_checked_eq :
-- imply
  rawMomentStateCoefficientList 361 = generatedStateCoefficients361 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients361_checked

/--
[coefficientChunk180_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean)
-/
@[path]
private lemma coefficientChunk180_checked_eq :
-- imply
  rawMomentCoefficientSmallList 360 2 = generatedCoefficientChunk180 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk180_checked


-- created on 2026-10-23
