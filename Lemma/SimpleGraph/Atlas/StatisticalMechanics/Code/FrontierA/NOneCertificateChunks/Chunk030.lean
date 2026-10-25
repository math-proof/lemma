import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk030.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts60_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma vCounts60_checked_eq :
-- imply
  rawMomentVCounts 60 = generatedVCounts60 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts60_checked

/--
[qCounts60_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma qCounts60_checked_eq :
-- imply
  rawMomentQCounts 60 = generatedQCounts60 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts60_checked

/--
[stateCoefficients60_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma stateCoefficients60_checked_eq :
-- imply
  rawMomentStateCoefficientList 60 = generatedStateCoefficients60 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients60_checked

/--
[vCounts61_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma vCounts61_checked_eq :
-- imply
  rawMomentVCounts 61 = generatedVCounts61 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts61_checked

/--
[qCounts61_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma qCounts61_checked_eq :
-- imply
  rawMomentQCounts 61 = generatedQCounts61 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts61_checked

/--
[stateCoefficients61_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma stateCoefficients61_checked_eq :
-- imply
  rawMomentStateCoefficientList 61 = generatedStateCoefficients61 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients61_checked

/--
[coefficientChunk30_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean)
-/
@[path]
private lemma coefficientChunk30_checked_eq :
-- imply
  rawMomentCoefficientSmallList 60 2 = generatedCoefficientChunk30 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk30_checked


-- created on 2026-10-23
