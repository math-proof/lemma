import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk045
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts90_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma vCounts90_checked_eq :
-- imply
  rawMomentVCounts 90 = generatedVCounts90 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts90_checked

/--
[qCounts90_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma qCounts90_checked_eq :
-- imply
  rawMomentQCounts 90 = generatedQCounts90 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts90_checked

/--
[stateCoefficients90_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma stateCoefficients90_checked_eq :
-- imply
  rawMomentStateCoefficientList 90 = generatedStateCoefficients90 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients90_checked

/--
[vCounts91_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma vCounts91_checked_eq :
-- imply
  rawMomentVCounts 91 = generatedVCounts91 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts91_checked

/--
[qCounts91_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma qCounts91_checked_eq :
-- imply
  rawMomentQCounts 91 = generatedQCounts91 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts91_checked

/--
[stateCoefficients91_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma stateCoefficients91_checked_eq :
-- imply
  rawMomentStateCoefficientList 91 = generatedStateCoefficients91 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients91_checked

/--
[coefficientChunk45_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean)
-/
@[path]
private lemma coefficientChunk45_checked_eq :
-- imply
  rawMomentCoefficientSmallList 90 2 = generatedCoefficientChunk45 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk45_checked


-- created on 2026-10-23
