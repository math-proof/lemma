import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk101.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts202_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma vCounts202_checked_eq :
-- imply
  rawMomentVCounts 202 = generatedVCounts202 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts202_checked

/--
[qCounts202_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma qCounts202_checked_eq :
-- imply
  rawMomentQCounts 202 = generatedQCounts202 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts202_checked

/--
[stateCoefficients202_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma stateCoefficients202_checked_eq :
-- imply
  rawMomentStateCoefficientList 202 = generatedStateCoefficients202 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients202_checked

/--
[vCounts203_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma vCounts203_checked_eq :
-- imply
  rawMomentVCounts 203 = generatedVCounts203 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts203_checked

/--
[qCounts203_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma qCounts203_checked_eq :
-- imply
  rawMomentQCounts 203 = generatedQCounts203 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts203_checked

/--
[stateCoefficients203_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma stateCoefficients203_checked_eq :
-- imply
  rawMomentStateCoefficientList 203 = generatedStateCoefficients203 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients203_checked

/--
[coefficientChunk101_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean)
-/
@[path]
private lemma coefficientChunk101_checked_eq :
-- imply
  rawMomentCoefficientSmallList 202 2 = generatedCoefficientChunk101 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk101_checked


-- created on 2026-10-23
