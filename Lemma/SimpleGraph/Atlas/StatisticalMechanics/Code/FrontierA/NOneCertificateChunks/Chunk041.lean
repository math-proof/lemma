import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk041.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts82_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma vCounts82_checked_eq :
-- imply
  rawMomentVCounts 82 = generatedVCounts82 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts82_checked

/--
[qCounts82_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma qCounts82_checked_eq :
-- imply
  rawMomentQCounts 82 = generatedQCounts82 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts82_checked

/--
[stateCoefficients82_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma stateCoefficients82_checked_eq :
-- imply
  rawMomentStateCoefficientList 82 = generatedStateCoefficients82 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients82_checked

/--
[vCounts83_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma vCounts83_checked_eq :
-- imply
  rawMomentVCounts 83 = generatedVCounts83 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts83_checked

/--
[qCounts83_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma qCounts83_checked_eq :
-- imply
  rawMomentQCounts 83 = generatedQCounts83 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts83_checked

/--
[stateCoefficients83_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma stateCoefficients83_checked_eq :
-- imply
  rawMomentStateCoefficientList 83 = generatedStateCoefficients83 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients83_checked

/--
[coefficientChunk41_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean)
-/
@[path]
private lemma coefficientChunk41_checked_eq :
-- imply
  rawMomentCoefficientSmallList 82 2 = generatedCoefficientChunk41 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk41_checked


-- created on 2026-10-23
