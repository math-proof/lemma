import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk100.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts200_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma vCounts200_checked_eq :
-- imply
  rawMomentVCounts 200 = generatedVCounts200 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts200_checked

/--
[qCounts200_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma qCounts200_checked_eq :
-- imply
  rawMomentQCounts 200 = generatedQCounts200 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts200_checked

/--
[stateCoefficients200_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma stateCoefficients200_checked_eq :
-- imply
  rawMomentStateCoefficientList 200 = generatedStateCoefficients200 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients200_checked

/--
[vCounts201_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma vCounts201_checked_eq :
-- imply
  rawMomentVCounts 201 = generatedVCounts201 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts201_checked

/--
[qCounts201_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma qCounts201_checked_eq :
-- imply
  rawMomentQCounts 201 = generatedQCounts201 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts201_checked

/--
[stateCoefficients201_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma stateCoefficients201_checked_eq :
-- imply
  rawMomentStateCoefficientList 201 = generatedStateCoefficients201 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients201_checked

/--
[coefficientChunk100_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk100.lean)
-/
@[path]
private lemma coefficientChunk100_checked_eq :
-- imply
  rawMomentCoefficientSmallList 200 2 = generatedCoefficientChunk100 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk100_checked


-- created on 2026-10-23
