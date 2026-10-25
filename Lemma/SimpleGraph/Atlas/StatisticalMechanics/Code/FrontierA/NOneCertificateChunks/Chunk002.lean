import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk002.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts4_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma vCounts4_checked_eq :
-- imply
  rawMomentVCounts 4 = generatedVCounts4 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts4_checked

/--
[qCounts4_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma qCounts4_checked_eq :
-- imply
  rawMomentQCounts 4 = generatedQCounts4 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts4_checked

/--
[stateCoefficients4_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma stateCoefficients4_checked_eq :
-- imply
  rawMomentStateCoefficientList 4 = generatedStateCoefficients4 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients4_checked

/--
[vCounts5_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma vCounts5_checked_eq :
-- imply
  rawMomentVCounts 5 = generatedVCounts5 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts5_checked

/--
[qCounts5_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma qCounts5_checked_eq :
-- imply
  rawMomentQCounts 5 = generatedQCounts5 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts5_checked

/--
[stateCoefficients5_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma stateCoefficients5_checked_eq :
-- imply
  rawMomentStateCoefficientList 5 = generatedStateCoefficients5 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients5_checked

/--
[coefficientChunk2_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean)
-/
@[path]
private lemma coefficientChunk2_checked_eq :
-- imply
  rawMomentCoefficientSmallList 4 2 = generatedCoefficientChunk2 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk2_checked


-- created on 2026-10-23
