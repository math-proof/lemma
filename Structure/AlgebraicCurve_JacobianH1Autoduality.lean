import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.AddChar

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor

variable {K F}


end Divisor


namespace H1Gm

variable {K F}


variable (K F)


variable {K F} in


variable [HasPrincipalDivisors K F]


end H1Gm


namespace H1mu

variable {K F}


variable (K F)


end H1mu

abbrev HomPic0Gm (n : ℕ) : Type _ := AddChar (Pic0.torsion K F n) K

namespace HomPic0Gm

variable {K F}


end HomPic0Gm

structure WeilPairingData (n : ℕ) where

  toHom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n)

  bijective : Function.Bijective toHom

namespace WeilPairingData

variable {K F}

def eval {n : ℕ} (e : WeilPairingData K F n) (x y : Pic0.torsion K F n) : K :=
  (Additive.toMul (e.toHom x)) y


end WeilPairingData

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace WeilPairingData

variable {n : ℕ} (e : WeilPairingData K F n)


end WeilPairingData

structure PrincipalPolarization (K F : Type*) [Field K] [Field F] [Algebra K F]
    (n : ℕ) extends WeilPairingData K F n where

  alternating : ∀ x : Pic0.torsion K F n, toWeilPairingData.eval x x = 1

end AlgebraicCurve
