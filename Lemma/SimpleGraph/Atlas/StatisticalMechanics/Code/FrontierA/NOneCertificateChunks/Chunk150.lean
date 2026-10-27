import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk150.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts300_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma vCounts300_checked_eq :
-- imply
  rawMomentVCounts 300 = generatedVCounts300 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts300_checked

/--
[qCounts300_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma qCounts300_checked_eq :
-- imply
  rawMomentQCounts 300 = generatedQCounts300 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts300_checked

/--
[stateCoefficients300_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma stateCoefficients300_checked_eq :
-- imply
  rawMomentStateCoefficientList 300 = generatedStateCoefficients300 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients300_checked

/--
[vCounts301_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma vCounts301_checked_eq :
-- imply
  rawMomentVCounts 301 = generatedVCounts301 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts301_checked

/--
[qCounts301_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma qCounts301_checked_eq :
-- imply
  rawMomentQCounts 301 = generatedQCounts301 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts301_checked

/--
[stateCoefficients301_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma stateCoefficients301_checked_eq :
-- imply
  rawMomentStateCoefficientList 301 = generatedStateCoefficients301 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients301_checked

/--
[coefficientChunk150_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean)
-/
@[path]
private lemma coefficientChunk150_checked_eq :
-- imply
  rawMomentCoefficientSmallList 300 2 = generatedCoefficientChunk150 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk150_checked


-- created on 2026-10-23
