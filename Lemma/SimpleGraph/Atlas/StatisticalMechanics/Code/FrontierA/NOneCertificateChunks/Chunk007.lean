import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk007.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts14_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma vCounts14_checked_eq :
-- imply
  rawMomentVCounts 14 = generatedVCounts14 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts14_checked

/--
[qCounts14_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma qCounts14_checked_eq :
-- imply
  rawMomentQCounts 14 = generatedQCounts14 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts14_checked

/--
[stateCoefficients14_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma stateCoefficients14_checked_eq :
-- imply
  rawMomentStateCoefficientList 14 = generatedStateCoefficients14 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients14_checked

/--
[vCounts15_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma vCounts15_checked_eq :
-- imply
  rawMomentVCounts 15 = generatedVCounts15 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts15_checked

/--
[qCounts15_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma qCounts15_checked_eq :
-- imply
  rawMomentQCounts 15 = generatedQCounts15 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts15_checked

/--
[stateCoefficients15_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma stateCoefficients15_checked_eq :
-- imply
  rawMomentStateCoefficientList 15 = generatedStateCoefficients15 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients15_checked

/--
[coefficientChunk7_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean)
-/
@[path]
private lemma coefficientChunk7_checked_eq :
-- imply
  rawMomentCoefficientSmallList 14 2 = generatedCoefficientChunk7 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk7_checked


-- created on 2026-10-23
