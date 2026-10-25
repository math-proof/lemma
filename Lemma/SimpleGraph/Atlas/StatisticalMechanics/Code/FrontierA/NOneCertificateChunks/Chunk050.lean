import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk050.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts100_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma vCounts100_checked_eq :
-- imply
  rawMomentVCounts 100 = generatedVCounts100 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts100_checked

/--
[qCounts100_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma qCounts100_checked_eq :
-- imply
  rawMomentQCounts 100 = generatedQCounts100 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts100_checked

/--
[stateCoefficients100_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma stateCoefficients100_checked_eq :
-- imply
  rawMomentStateCoefficientList 100 = generatedStateCoefficients100 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients100_checked

/--
[vCounts101_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma vCounts101_checked_eq :
-- imply
  rawMomentVCounts 101 = generatedVCounts101 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts101_checked

/--
[qCounts101_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma qCounts101_checked_eq :
-- imply
  rawMomentQCounts 101 = generatedQCounts101 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts101_checked

/--
[stateCoefficients101_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma stateCoefficients101_checked_eq :
-- imply
  rawMomentStateCoefficientList 101 = generatedStateCoefficients101 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients101_checked

/--
[coefficientChunk50_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk050.lean)
-/
@[path]
private lemma coefficientChunk50_checked_eq :
-- imply
  rawMomentCoefficientSmallList 100 2 = generatedCoefficientChunk50 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk50_checked


-- created on 2026-10-23
