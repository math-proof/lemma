import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk011
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts22_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma vCounts22_checked_eq :
-- imply
  rawMomentVCounts 22 = generatedVCounts22 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts22_checked

/--
[qCounts22_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma qCounts22_checked_eq :
-- imply
  rawMomentQCounts 22 = generatedQCounts22 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts22_checked

/--
[stateCoefficients22_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma stateCoefficients22_checked_eq :
-- imply
  rawMomentStateCoefficientList 22 = generatedStateCoefficients22 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients22_checked

/--
[vCounts23_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma vCounts23_checked_eq :
-- imply
  rawMomentVCounts 23 = generatedVCounts23 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts23_checked

/--
[qCounts23_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma qCounts23_checked_eq :
-- imply
  rawMomentQCounts 23 = generatedQCounts23 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts23_checked

/--
[stateCoefficients23_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma stateCoefficients23_checked_eq :
-- imply
  rawMomentStateCoefficientList 23 = generatedStateCoefficients23 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients23_checked

/--
[coefficientChunk11_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean)
-/
@[path]
private lemma coefficientChunk11_checked_eq :
-- imply
  rawMomentCoefficientSmallList 22 2 = generatedCoefficientChunk11 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk11_checked


-- created on 2026-10-23
