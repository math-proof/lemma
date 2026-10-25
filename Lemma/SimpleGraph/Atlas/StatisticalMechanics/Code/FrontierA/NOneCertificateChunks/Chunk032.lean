import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk032.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts64_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma vCounts64_checked_eq :
-- imply
  rawMomentVCounts 64 = generatedVCounts64 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts64_checked

/--
[qCounts64_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma qCounts64_checked_eq :
-- imply
  rawMomentQCounts 64 = generatedQCounts64 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts64_checked

/--
[stateCoefficients64_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma stateCoefficients64_checked_eq :
-- imply
  rawMomentStateCoefficientList 64 = generatedStateCoefficients64 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients64_checked

/--
[vCounts65_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma vCounts65_checked_eq :
-- imply
  rawMomentVCounts 65 = generatedVCounts65 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts65_checked

/--
[qCounts65_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma qCounts65_checked_eq :
-- imply
  rawMomentQCounts 65 = generatedQCounts65 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts65_checked

/--
[stateCoefficients65_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma stateCoefficients65_checked_eq :
-- imply
  rawMomentStateCoefficientList 65 = generatedStateCoefficients65 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients65_checked

/--
[coefficientChunk32_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean)
-/
@[path]
private lemma coefficientChunk32_checked_eq :
-- imply
  rawMomentCoefficientSmallList 64 2 = generatedCoefficientChunk32 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk32_checked


-- created on 2026-10-23
