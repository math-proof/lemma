import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk125.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts250_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma vCounts250_checked_eq :
-- imply
  rawMomentVCounts 250 = generatedVCounts250 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts250_checked

/--
[qCounts250_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma qCounts250_checked_eq :
-- imply
  rawMomentQCounts 250 = generatedQCounts250 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts250_checked

/--
[stateCoefficients250_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma stateCoefficients250_checked_eq :
-- imply
  rawMomentStateCoefficientList 250 = generatedStateCoefficients250 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients250_checked

/--
[vCounts251_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma vCounts251_checked_eq :
-- imply
  rawMomentVCounts 251 = generatedVCounts251 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts251_checked

/--
[qCounts251_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma qCounts251_checked_eq :
-- imply
  rawMomentQCounts 251 = generatedQCounts251 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts251_checked

/--
[stateCoefficients251_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma stateCoefficients251_checked_eq :
-- imply
  rawMomentStateCoefficientList 251 = generatedStateCoefficients251 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients251_checked

/--
[coefficientChunk125_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean)
-/
@[path]
private lemma coefficientChunk125_checked_eq :
-- imply
  rawMomentCoefficientSmallList 250 2 = generatedCoefficientChunk125 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk125_checked


-- created on 2026-10-23
