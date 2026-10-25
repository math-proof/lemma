import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk222.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts444_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma vCounts444_checked_eq :
-- imply
  rawMomentVCounts 444 = generatedVCounts444 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts444_checked

/--
[qCounts444_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma qCounts444_checked_eq :
-- imply
  rawMomentQCounts 444 = generatedQCounts444 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts444_checked

/--
[stateCoefficients444_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma stateCoefficients444_checked_eq :
-- imply
  rawMomentStateCoefficientList 444 = generatedStateCoefficients444 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients444_checked

/--
[vCounts445_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma vCounts445_checked_eq :
-- imply
  rawMomentVCounts 445 = generatedVCounts445 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts445_checked

/--
[qCounts445_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma qCounts445_checked_eq :
-- imply
  rawMomentQCounts 445 = generatedQCounts445 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts445_checked

/--
[stateCoefficients445_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma stateCoefficients445_checked_eq :
-- imply
  rawMomentStateCoefficientList 445 = generatedStateCoefficients445 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients445_checked

/--
[coefficientChunk222_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean)
-/
@[path]
private lemma coefficientChunk222_checked_eq :
-- imply
  rawMomentCoefficientSmallList 444 2 = generatedCoefficientChunk222 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk222_checked


-- created on 2026-10-23
