import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk031.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts62_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma vCounts62_checked_eq :
-- imply
  rawMomentVCounts 62 = generatedVCounts62 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts62_checked

/--
[qCounts62_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma qCounts62_checked_eq :
-- imply
  rawMomentQCounts 62 = generatedQCounts62 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts62_checked

/--
[stateCoefficients62_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma stateCoefficients62_checked_eq :
-- imply
  rawMomentStateCoefficientList 62 = generatedStateCoefficients62 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients62_checked

/--
[vCounts63_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma vCounts63_checked_eq :
-- imply
  rawMomentVCounts 63 = generatedVCounts63 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts63_checked

/--
[qCounts63_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma qCounts63_checked_eq :
-- imply
  rawMomentQCounts 63 = generatedQCounts63 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts63_checked

/--
[stateCoefficients63_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma stateCoefficients63_checked_eq :
-- imply
  rawMomentStateCoefficientList 63 = generatedStateCoefficients63 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients63_checked

/--
[coefficientChunk31_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean)
-/
@[path]
private lemma coefficientChunk31_checked_eq :
-- imply
  rawMomentCoefficientSmallList 62 2 = generatedCoefficientChunk31 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk31_checked


-- created on 2026-10-23
