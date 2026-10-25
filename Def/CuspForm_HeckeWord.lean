import Mathlib.Algebra.FreeAlgebra
import Instance.CuspForm_HeckeAlgebra
import Instance.Gamma0HeckeOperatorHom

open CongruenceSubgroup

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) [DecidablePred (· ∈ S)]

noncomputable def heckeWordGenForms (n : ℕ) : Module.End ℂ (CuspForm (Gamma0 N) k) :=
  if h : n.Prime ∧ n ∉ S then
    (if hn : n ∣ N then heckeULin k hn else heckeTLin k h.1 hn)
  else 0


noncomputable def heckeWordForms : FreeAlgebra ℤ ℕ →ₐ[ℤ] Module.End ℂ (CuspForm (Gamma0 N) k) :=
  FreeAlgebra.lift ℤ (heckeWordGenForms N k S)

end CuspForm

namespace HeckeEis

variable (N : ℕ) (A : Type*) [AddCommGroup A] (S : Set ℕ) [DecidablePred (· ∈ S)]

noncomputable def heckeWordGenHom (n : ℕ) : Module.End ℤ (Additive (Gamma0 N) →+ A) :=
  if h : n.Prime ∧ n ∉ S then
    (haveI : NeZero n := ⟨h.1.ne_zero⟩; (heckeOperatorHom N n A).toIntLinearMap)
  else 0


noncomputable def heckeWordHom : FreeAlgebra ℤ ℕ →ₐ[ℤ] Module.End ℤ (Additive (Gamma0 N) →+ A) :=
  FreeAlgebra.lift ℤ (heckeWordGenHom N A S)

end HeckeEis
