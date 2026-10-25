import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk200.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts400_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma vCounts400_checked_eq :
-- imply
  rawMomentVCounts 400 = generatedVCounts400 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts400_checked

/--
[qCounts400_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma qCounts400_checked_eq :
-- imply
  rawMomentQCounts 400 = generatedQCounts400 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts400_checked

/--
[stateCoefficients400_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma stateCoefficients400_checked_eq :
-- imply
  rawMomentStateCoefficientList 400 = generatedStateCoefficients400 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients400_checked

/--
[vCounts401_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma vCounts401_checked_eq :
-- imply
  rawMomentVCounts 401 = generatedVCounts401 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts401_checked

/--
[qCounts401_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma qCounts401_checked_eq :
-- imply
  rawMomentQCounts 401 = generatedQCounts401 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts401_checked

/--
[stateCoefficients401_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma stateCoefficients401_checked_eq :
-- imply
  rawMomentStateCoefficientList 401 = generatedStateCoefficients401 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients401_checked

/--
[coefficientChunk200_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean)
-/
@[path]
private lemma coefficientChunk200_checked_eq :
-- imply
  rawMomentCoefficientSmallList 400 2 = generatedCoefficientChunk200 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk200_checked


-- created on 2026-10-23
