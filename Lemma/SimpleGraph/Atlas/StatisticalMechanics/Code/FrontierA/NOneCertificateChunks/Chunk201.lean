import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk201.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts402_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma vCounts402_checked_eq :
-- imply
  rawMomentVCounts 402 = generatedVCounts402 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts402_checked

/--
[qCounts402_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma qCounts402_checked_eq :
-- imply
  rawMomentQCounts 402 = generatedQCounts402 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts402_checked

/--
[stateCoefficients402_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma stateCoefficients402_checked_eq :
-- imply
  rawMomentStateCoefficientList 402 = generatedStateCoefficients402 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients402_checked

/--
[vCounts403_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma vCounts403_checked_eq :
-- imply
  rawMomentVCounts 403 = generatedVCounts403 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts403_checked

/--
[qCounts403_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma qCounts403_checked_eq :
-- imply
  rawMomentQCounts 403 = generatedQCounts403 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts403_checked

/--
[stateCoefficients403_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma stateCoefficients403_checked_eq :
-- imply
  rawMomentStateCoefficientList 403 = generatedStateCoefficients403 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients403_checked

/--
[coefficientChunk201_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk201.lean)
-/
@[path]
private lemma coefficientChunk201_checked_eq :
-- imply
  rawMomentCoefficientSmallList 402 2 = generatedCoefficientChunk201 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk201_checked


-- created on 2026-10-23
