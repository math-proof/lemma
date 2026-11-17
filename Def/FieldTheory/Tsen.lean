/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Tsen.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MathlibExt.FieldTheory.TsenWanted

universe u v w

noncomputable def tsenGen (k : Type u) [Field k] (n N : ℕ) (i : Fin n) :
    Polynomial (MvPolynomial (Fin n × Fin (N + 1)) k) :=
  Finset.sum Finset.univ (fun j : Fin (N + 1) =>
    Polynomial.C (MvPolynomial.X (i, j)) * Polynomial.X ^ (j.val))

noncomputable def tsenGeneric (k : Type u) [Field k] (n N : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) :
    Polynomial (MvPolynomial (Fin n × Fin (N + 1)) k) :=
  MvPolynomial.eval₂
    (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k))
    (tsenGen k n N) g

noncomputable def tsenSpec (k : Type u) [Field k] (n N : ℕ)
    (a : Fin n × Fin (N + 1) → k) (i : Fin n) : Polynomial k :=
  Finset.sum Finset.univ (fun j : Fin (N + 1) =>
    Polynomial.C (a (i, j)) * Polynomial.X ^ (j.val))

end MathlibExt.FieldTheory.TsenWanted
end
