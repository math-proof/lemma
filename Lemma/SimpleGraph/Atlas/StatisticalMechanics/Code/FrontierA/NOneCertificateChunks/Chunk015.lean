import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk015.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts30_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma vCounts30_checked_eq :
-- imply
  rawMomentVCounts 30 = generatedVCounts30 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts30_checked

/--
[qCounts30_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma qCounts30_checked_eq :
-- imply
  rawMomentQCounts 30 = generatedQCounts30 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts30_checked

/--
[stateCoefficients30_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma stateCoefficients30_checked_eq :
-- imply
  rawMomentStateCoefficientList 30 = generatedStateCoefficients30 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients30_checked

/--
[vCounts31_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma vCounts31_checked_eq :
-- imply
  rawMomentVCounts 31 = generatedVCounts31 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts31_checked

/--
[qCounts31_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma qCounts31_checked_eq :
-- imply
  rawMomentQCounts 31 = generatedQCounts31 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts31_checked

/--
[stateCoefficients31_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma stateCoefficients31_checked_eq :
-- imply
  rawMomentStateCoefficientList 31 = generatedStateCoefficients31 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients31_checked

/--
[coefficientChunk15_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean)
-/
@[path]
private lemma coefficientChunk15_checked_eq :
-- imply
  rawMomentCoefficientSmallList 30 2 = generatedCoefficientChunk15 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk15_checked


-- created on 2026-10-23
