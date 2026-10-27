import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk075.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts150_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma vCounts150_checked_eq :
-- imply
  rawMomentVCounts 150 = generatedVCounts150 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts150_checked

/--
[qCounts150_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma qCounts150_checked_eq :
-- imply
  rawMomentQCounts 150 = generatedQCounts150 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts150_checked

/--
[stateCoefficients150_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma stateCoefficients150_checked_eq :
-- imply
  rawMomentStateCoefficientList 150 = generatedStateCoefficients150 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients150_checked

/--
[vCounts151_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma vCounts151_checked_eq :
-- imply
  rawMomentVCounts 151 = generatedVCounts151 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts151_checked

/--
[qCounts151_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma qCounts151_checked_eq :
-- imply
  rawMomentQCounts 151 = generatedQCounts151 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts151_checked

/--
[stateCoefficients151_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma stateCoefficients151_checked_eq :
-- imply
  rawMomentStateCoefficientList 151 = generatedStateCoefficients151 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients151_checked

/--
[coefficientChunk75_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk075.lean)
-/
@[path]
private lemma coefficientChunk75_checked_eq :
-- imply
  rawMomentCoefficientSmallList 150 2 = generatedCoefficientChunk75 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk75_checked


-- created on 2026-10-23
