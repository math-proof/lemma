import Mathlib
import Instance.ExtEndgame_ProductionDatum
import Instance.EllipticCurve_FrobeniusTrace
import Lemma.Deformations.Frobenius

set_option autoImplicit false

open ExtCitation
open scoped NNReal

namespace ExtCitation.LocalLevel


section Local

variable (q : ℕ) [Fact q.Prime]

abbrev OO : Type := ↥(padicIntegers q)

abbrev GG : Type := PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q


end Local

section LevelW

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

noncomputable abbrev Rw : ValuationSubring Kw := (padicIntegers q).comap (algebraMap Kw (PadicAlgCl q))

noncomputable abbrev Gw : Subgroup (GG q) := Kw.fixingSubgroup


end LevelW

section Residues

variable (q : ℕ) [Fact q.Prime]

abbrev kbar : Type := IsLocalRing.ResidueField (OO q)


end Residues

section DegreeBound

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

end DegreeBound

section Transport

variable (q : ℕ) [Fact q.Prime]

noncomputable abbrev rD : GG q →* ↥((padicPlace q).decompositionSubgroup ℚ) :=
  (localGaloisToGlobal q).codRestrict _ (localGaloisToGlobal_mem_decompositionSubgroup q)

end Transport

section ResidueMap

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q))

noncomputable abbrev resw (x : Rw q Kw) : kbar q := IsLocalRing.residue (OO q) (algebraMap (Rw q Kw) (OO q) x)

end ResidueMap

section Commute

variable (q : ℕ) [Fact q.Prime]

end Commute

section MoveLikeFrobenius

variable (q : ℕ) [Fact q.Prime]

end MoveLikeFrobenius

end ExtCitation.LocalLevel
