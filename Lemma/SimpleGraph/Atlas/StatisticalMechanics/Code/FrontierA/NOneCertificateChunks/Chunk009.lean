import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk009.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts18_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma vCounts18_checked_eq :
-- imply
  rawMomentVCounts 18 = generatedVCounts18 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts18_checked

/--
[qCounts18_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma qCounts18_checked_eq :
-- imply
  rawMomentQCounts 18 = generatedQCounts18 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts18_checked

/--
[stateCoefficients18_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma stateCoefficients18_checked_eq :
-- imply
  rawMomentStateCoefficientList 18 = generatedStateCoefficients18 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients18_checked

/--
[vCounts19_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma vCounts19_checked_eq :
-- imply
  rawMomentVCounts 19 = generatedVCounts19 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts19_checked

/--
[qCounts19_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma qCounts19_checked_eq :
-- imply
  rawMomentQCounts 19 = generatedQCounts19 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts19_checked

/--
[stateCoefficients19_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma stateCoefficients19_checked_eq :
-- imply
  rawMomentStateCoefficientList 19 = generatedStateCoefficients19 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients19_checked

/--
[coefficientChunk9_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean)
-/
@[path]
private lemma coefficientChunk9_checked_eq :
-- imply
  rawMomentCoefficientSmallList 18 2 = generatedCoefficientChunk9 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk9_checked


-- created on 2026-10-23
