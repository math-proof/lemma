import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk128.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts256_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma vCounts256_checked_eq :
-- imply
  rawMomentVCounts 256 = generatedVCounts256 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts256_checked

/--
[qCounts256_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma qCounts256_checked_eq :
-- imply
  rawMomentQCounts 256 = generatedQCounts256 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts256_checked

/--
[stateCoefficients256_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma stateCoefficients256_checked_eq :
-- imply
  rawMomentStateCoefficientList 256 = generatedStateCoefficients256 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients256_checked

/--
[vCounts257_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma vCounts257_checked_eq :
-- imply
  rawMomentVCounts 257 = generatedVCounts257 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts257_checked

/--
[qCounts257_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma qCounts257_checked_eq :
-- imply
  rawMomentQCounts 257 = generatedQCounts257 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts257_checked

/--
[stateCoefficients257_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma stateCoefficients257_checked_eq :
-- imply
  rawMomentStateCoefficientList 257 = generatedStateCoefficients257 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients257_checked

/--
[coefficientChunk128_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk128.lean)
-/
@[path]
private lemma coefficientChunk128_checked_eq :
-- imply
  rawMomentCoefficientSmallList 256 2 = generatedCoefficientChunk128 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk128_checked


-- created on 2026-10-23
