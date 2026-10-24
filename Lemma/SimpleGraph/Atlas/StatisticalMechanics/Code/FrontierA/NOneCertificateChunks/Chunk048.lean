import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk048
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[vCounts96_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma vCounts96_checked_eq :
-- imply
  rawMomentVCounts 96 = generatedVCounts96 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts96_checked

/--
[qCounts96_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma qCounts96_checked_eq :
-- imply
  rawMomentQCounts 96 = generatedQCounts96 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts96_checked

/--
[stateCoefficients96_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma stateCoefficients96_checked_eq :
-- imply
  rawMomentStateCoefficientList 96 = generatedStateCoefficients96 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients96_checked

/--
[vCounts97_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma vCounts97_checked_eq :
-- imply
  rawMomentVCounts 97 = generatedVCounts97 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.vCounts97_checked

/--
[qCounts97_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma qCounts97_checked_eq :
-- imply
  rawMomentQCounts 97 = generatedQCounts97 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.qCounts97_checked

/--
[stateCoefficients97_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma stateCoefficients97_checked_eq :
-- imply
  rawMomentStateCoefficientList 97 = generatedStateCoefficients97 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.stateCoefficients97_checked

/--
[coefficientChunk48_checked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk048.lean)
-/
@[path]
private lemma coefficientChunk48_checked_eq :
-- imply
  rawMomentCoefficientSmallList 96 2 = generatedCoefficientChunk48 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.coefficientChunk48_checked


-- created on 2026-10-23
