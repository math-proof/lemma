import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk000
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts0_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma vCounts0_checked_eq :
-- imply
  rawMomentVCounts 0 = generatedVCounts0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts0_checked

/--
[qCounts0_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma qCounts0_checked_eq :
-- imply
  rawMomentQCounts 0 = generatedQCounts0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts0_checked

/--
[stateCoefficients0_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma stateCoefficients0_checked_eq :
-- imply
  rawMomentStateCoefficientList 0 = generatedStateCoefficients0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients0_checked

/--
[vCounts1_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma vCounts1_checked_eq :
-- imply
  rawMomentVCounts 1 = generatedVCounts1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts1_checked

/--
[qCounts1_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma qCounts1_checked_eq :
-- imply
  rawMomentQCounts 1 = generatedQCounts1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts1_checked

/--
[stateCoefficients1_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma stateCoefficients1_checked_eq :
-- imply
  rawMomentStateCoefficientList 1 = generatedStateCoefficients1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients1_checked

/--
[coefficientChunk0_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean)
-/
@[path]
private lemma coefficientChunk0_checked_eq :
-- imply
  rawMomentCoefficientSmallList 0 2 = generatedCoefficientChunk0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk0_checked


-- created on 2026-10-23
