import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk110
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts220_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma vCounts220_checked_eq :
-- imply
  rawMomentVCounts 220 = generatedVCounts220 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts220_checked

/--
[qCounts220_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma qCounts220_checked_eq :
-- imply
  rawMomentQCounts 220 = generatedQCounts220 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts220_checked

/--
[stateCoefficients220_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma stateCoefficients220_checked_eq :
-- imply
  rawMomentStateCoefficientList 220 = generatedStateCoefficients220 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients220_checked

/--
[vCounts221_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma vCounts221_checked_eq :
-- imply
  rawMomentVCounts 221 = generatedVCounts221 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts221_checked

/--
[qCounts221_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma qCounts221_checked_eq :
-- imply
  rawMomentQCounts 221 = generatedQCounts221 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts221_checked

/--
[stateCoefficients221_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma stateCoefficients221_checked_eq :
-- imply
  rawMomentStateCoefficientList 221 = generatedStateCoefficients221 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients221_checked

/--
[coefficientChunk110_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk110.lean)
-/
@[path]
private lemma coefficientChunk110_checked_eq :
-- imply
  rawMomentCoefficientSmallList 220 2 = generatedCoefficientChunk110 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk110_checked


-- created on 2026-10-23
