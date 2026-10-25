import Mathlib
import Theorem.Analysis.Misc.erdos_707.Part2


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

/--
{given -show}`b, c, d`
Given a perfect difference set {name}`B` and an element {name}`a` not in {name}`B`, the function
{lean}`f (a := a)` maps each {lean}`b ∈ B` to the unique {lean}`c ∈ B` such that {lean}`a - b = c -
d` for some {lean}`d ∈ B`.
-/
noncomputable def f {a:ZMod N} (ha: a ∉ B) (b:B): B :=
    (hdiff (a-b.val) (by grind)).choose.1

/--
{given -show}`d`
Though not defined in Theorem 8, it is convenient to also introduce the companion function {lean}`g (a := a)`, defined to be the {name}`d` element such that {lean}`a - b = f (a := a) ha b - d`.
-/
noncomputable def g {a:ZMod N} (ha: a ∉ B) (b:B): B :=
    (hdiff (a-b.val) (by grind)).choose.2

end Mainstep
