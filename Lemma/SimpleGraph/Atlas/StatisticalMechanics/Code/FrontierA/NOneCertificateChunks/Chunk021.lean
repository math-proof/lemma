import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk021.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts42_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma vCounts42_checked_eq :
-- imply
  rawMomentVCounts 42 = generatedVCounts42 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts42_checked

/--
[qCounts42_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma qCounts42_checked_eq :
-- imply
  rawMomentQCounts 42 = generatedQCounts42 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts42_checked

/--
[stateCoefficients42_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma stateCoefficients42_checked_eq :
-- imply
  rawMomentStateCoefficientList 42 = generatedStateCoefficients42 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients42_checked

/--
[vCounts43_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma vCounts43_checked_eq :
-- imply
  rawMomentVCounts 43 = generatedVCounts43 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts43_checked

/--
[qCounts43_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma qCounts43_checked_eq :
-- imply
  rawMomentQCounts 43 = generatedQCounts43 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts43_checked

/--
[stateCoefficients43_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma stateCoefficients43_checked_eq :
-- imply
  rawMomentStateCoefficientList 43 = generatedStateCoefficients43 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients43_checked

/--
[coefficientChunk21_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean)
-/
@[path]
private lemma coefficientChunk21_checked_eq :
-- imply
  rawMomentCoefficientSmallList 42 2 = generatedCoefficientChunk21 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk21_checked


-- created on 2026-10-23
