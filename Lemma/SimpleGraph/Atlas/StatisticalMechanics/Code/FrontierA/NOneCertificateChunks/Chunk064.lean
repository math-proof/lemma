import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk064
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts128_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma vCounts128_checked_eq :
-- imply
  rawMomentVCounts 128 = generatedVCounts128 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts128_checked

/--
[qCounts128_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma qCounts128_checked_eq :
-- imply
  rawMomentQCounts 128 = generatedQCounts128 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts128_checked

/--
[stateCoefficients128_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma stateCoefficients128_checked_eq :
-- imply
  rawMomentStateCoefficientList 128 = generatedStateCoefficients128 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients128_checked

/--
[vCounts129_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma vCounts129_checked_eq :
-- imply
  rawMomentVCounts 129 = generatedVCounts129 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts129_checked

/--
[qCounts129_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma qCounts129_checked_eq :
-- imply
  rawMomentQCounts 129 = generatedQCounts129 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts129_checked

/--
[stateCoefficients129_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma stateCoefficients129_checked_eq :
-- imply
  rawMomentStateCoefficientList 129 = generatedStateCoefficients129 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients129_checked

/--
[coefficientChunk64_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean)
-/
@[path]
private lemma coefficientChunk64_checked_eq :
-- imply
  rawMomentCoefficientSmallList 128 2 = generatedCoefficientChunk64 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk64_checked


-- created on 2026-10-23
