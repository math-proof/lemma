import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk040.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts80_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma vCounts80_checked_eq :
-- imply
  rawMomentVCounts 80 = generatedVCounts80 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts80_checked

/--
[qCounts80_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma qCounts80_checked_eq :
-- imply
  rawMomentQCounts 80 = generatedQCounts80 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts80_checked

/--
[stateCoefficients80_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma stateCoefficients80_checked_eq :
-- imply
  rawMomentStateCoefficientList 80 = generatedStateCoefficients80 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients80_checked

/--
[vCounts81_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma vCounts81_checked_eq :
-- imply
  rawMomentVCounts 81 = generatedVCounts81 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts81_checked

/--
[qCounts81_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma qCounts81_checked_eq :
-- imply
  rawMomentQCounts 81 = generatedQCounts81 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts81_checked

/--
[stateCoefficients81_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma stateCoefficients81_checked_eq :
-- imply
  rawMomentStateCoefficientList 81 = generatedStateCoefficients81 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients81_checked

/--
[coefficientChunk40_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk040.lean)
-/
@[path]
private lemma coefficientChunk40_checked_eq :
-- imply
  rawMomentCoefficientSmallList 80 2 = generatedCoefficientChunk40 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk40_checked


-- created on 2026-10-23
