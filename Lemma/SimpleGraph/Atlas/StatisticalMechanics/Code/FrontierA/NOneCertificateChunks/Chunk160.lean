import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk160.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts320_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma vCounts320_checked_eq :
-- imply
  rawMomentVCounts 320 = generatedVCounts320 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts320_checked

/--
[qCounts320_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma qCounts320_checked_eq :
-- imply
  rawMomentQCounts 320 = generatedQCounts320 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts320_checked

/--
[stateCoefficients320_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma stateCoefficients320_checked_eq :
-- imply
  rawMomentStateCoefficientList 320 = generatedStateCoefficients320 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients320_checked

/--
[vCounts321_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma vCounts321_checked_eq :
-- imply
  rawMomentVCounts 321 = generatedVCounts321 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts321_checked

/--
[qCounts321_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma qCounts321_checked_eq :
-- imply
  rawMomentQCounts 321 = generatedQCounts321 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts321_checked

/--
[stateCoefficients321_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma stateCoefficients321_checked_eq :
-- imply
  rawMomentStateCoefficientList 321 = generatedStateCoefficients321 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients321_checked

/--
[coefficientChunk160_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean)
-/
@[path]
private lemma coefficientChunk160_checked_eq :
-- imply
  rawMomentCoefficientSmallList 320 2 = generatedCoefficientChunk160 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk160_checked


-- created on 2026-10-23
