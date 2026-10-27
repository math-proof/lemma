import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk043.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts86_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma vCounts86_checked_eq :
-- imply
  rawMomentVCounts 86 = generatedVCounts86 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts86_checked

/--
[qCounts86_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma qCounts86_checked_eq :
-- imply
  rawMomentQCounts 86 = generatedQCounts86 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts86_checked

/--
[stateCoefficients86_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma stateCoefficients86_checked_eq :
-- imply
  rawMomentStateCoefficientList 86 = generatedStateCoefficients86 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients86_checked

/--
[vCounts87_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma vCounts87_checked_eq :
-- imply
  rawMomentVCounts 87 = generatedVCounts87 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts87_checked

/--
[qCounts87_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma qCounts87_checked_eq :
-- imply
  rawMomentQCounts 87 = generatedQCounts87 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts87_checked

/--
[stateCoefficients87_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma stateCoefficients87_checked_eq :
-- imply
  rawMomentStateCoefficientList 87 = generatedStateCoefficients87 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients87_checked

/--
[coefficientChunk43_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk043.lean)
-/
@[path]
private lemma coefficientChunk43_checked_eq :
-- imply
  rawMomentCoefficientSmallList 86 2 = generatedCoefficientChunk43 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk43_checked


-- created on 2026-10-23
