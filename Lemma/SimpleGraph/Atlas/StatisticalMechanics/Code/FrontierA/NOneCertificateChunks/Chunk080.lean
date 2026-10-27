import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk080.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts160_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma vCounts160_checked_eq :
-- imply
  rawMomentVCounts 160 = generatedVCounts160 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts160_checked

/--
[qCounts160_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma qCounts160_checked_eq :
-- imply
  rawMomentQCounts 160 = generatedQCounts160 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts160_checked

/--
[stateCoefficients160_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma stateCoefficients160_checked_eq :
-- imply
  rawMomentStateCoefficientList 160 = generatedStateCoefficients160 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients160_checked

/--
[vCounts161_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma vCounts161_checked_eq :
-- imply
  rawMomentVCounts 161 = generatedVCounts161 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts161_checked

/--
[qCounts161_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma qCounts161_checked_eq :
-- imply
  rawMomentQCounts 161 = generatedQCounts161 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts161_checked

/--
[stateCoefficients161_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma stateCoefficients161_checked_eq :
-- imply
  rawMomentStateCoefficientList 161 = generatedStateCoefficients161 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients161_checked

/--
[coefficientChunk80_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk080.lean)
-/
@[path]
private lemma coefficientChunk80_checked_eq :
-- imply
  rawMomentCoefficientSmallList 160 2 = generatedCoefficientChunk80 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk80_checked


-- created on 2026-10-23
