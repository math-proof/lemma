import Mathlib.Algebra.Exact
import Mathlib.GroupTheory.Index

set_option autoImplicit false

noncomputable section

namespace ModularCurve

universe u

structure FppfKummerData (p : ℕ) where

  H0Gm : Type u

  H1mu : Type u

  H1Z : Type u
  [instH0Gm : AddCommGroup H0Gm]
  [instH1mu : AddCommGroup H1mu]
  [instH1Z : AddCommGroup H1Z]

  kummerDelta : H0Gm →+ H1mu

  kummerDelta_surjective : Function.Surjective kummerDelta

  h1Z_subsingleton : Subsingleton H1Z

  h1mu_subsingleton : Odd p → Subsingleton H1mu

structure JKummerRow (p m : ℕ) (M : Type u) [AddCommGroup M] where

  M0 : Type u

  H1Jtors : Type u

  H1J : Type u
  [instM0 : AddCommGroup M0]
  [instH1Jtors : AddCommGroup H1Jtors]
  [instH1J : AddCommGroup H1J]

  toM : M0 →+ M

  toM_injective : Function.Injective toM

  toM_finiteIndex : toM.range.FiniteIndex

  delta : M0 →+ H1Jtors

  push : H1Jtors →+ H1J

  delta_ker :
    delta.ker = (((p ^ m : ℤ) • (AddMonoidHom.id M0 : M0 →+ M0)).range : AddSubgroup M0)

  exact_delta_push : Function.Exact delta push

  push_range : push.range = (AddMonoidHom.ker ((p ^ m : ℤ) • AddMonoidHom.id H1J) : AddSubgroup H1J)

end ModularCurve
