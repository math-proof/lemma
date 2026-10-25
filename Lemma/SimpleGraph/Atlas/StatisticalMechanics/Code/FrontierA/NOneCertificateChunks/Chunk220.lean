import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk220.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts440_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma vCounts440_checked_eq :
-- imply
  rawMomentVCounts 440 = generatedVCounts440 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts440_checked

/--
[qCounts440_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma qCounts440_checked_eq :
-- imply
  rawMomentQCounts 440 = generatedQCounts440 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts440_checked

/--
[stateCoefficients440_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma stateCoefficients440_checked_eq :
-- imply
  rawMomentStateCoefficientList 440 = generatedStateCoefficients440 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients440_checked

/--
[vCounts441_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma vCounts441_checked_eq :
-- imply
  rawMomentVCounts 441 = generatedVCounts441 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts441_checked

/--
[qCounts441_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma qCounts441_checked_eq :
-- imply
  rawMomentQCounts 441 = generatedQCounts441 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts441_checked

/--
[stateCoefficients441_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma stateCoefficients441_checked_eq :
-- imply
  rawMomentStateCoefficientList 441 = generatedStateCoefficients441 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients441_checked

/--
[coefficientChunk220_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean)
-/
@[path]
private lemma coefficientChunk220_checked_eq :
-- imply
  rawMomentCoefficientSmallList 440 2 = generatedCoefficientChunk220 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk220_checked


-- created on 2026-10-23
