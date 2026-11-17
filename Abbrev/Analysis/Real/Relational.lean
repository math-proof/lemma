import Theorem.Rat.Div.eq.One.of.Ne_0
import Theorem.Rat.InvDiv.eq.Div
import Theorem.Rat.MulDivS.eq.Div.of.Ne_0
import Theorem.Hyperreal.EqSt.of.InfinitesimalSub
import Theorem.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Theorem.Hyperreal.EqSt_0.of.Infinite
import Theorem.Hyperreal.StInv.eq.Inv.of.EqSt
import Theorem.Hyperreal.Infinitesimal0
import Theorem.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
import Theorem.Nat.NotLt.is.Ge
open Hyperreal Rat Nat Int


abbrev XEq (α : Sort u) := Setoid α

namespace XEq
export Setoid (symm trans)
end XEq

