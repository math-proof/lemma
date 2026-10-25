import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.AddChar
import Structure.AlgebraicCurve_JacobianH1Autoduality

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor

variable {K F}

end Divisor

abbrev H1Gm : Type _ := Pic K F

namespace H1Gm

variable {K F}

abbrev mk (D : Divisor K F) : H1Gm K F := QuotientAddGroup.mk D

end H1Gm

abbrev H1mu (n : ℕ) : Type _ := Pic0.torsion K F n

namespace H1mu

variable {K F}

end H1mu


namespace HomPic0Gm

variable {K F}

end HomPic0Gm


namespace WeilPairingData

variable {K F}


end WeilPairingData

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace WeilPairingData

variable {n : ℕ} (e : WeilPairingData K F n)

end WeilPairingData


end AlgebraicCurve
