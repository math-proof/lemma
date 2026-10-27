import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.InvDiv.eq.Div
import Lemma.Rat.MulDivS.eq.Div.of.Ne_0
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StInv.eq.Inv.of.EqSt
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSubDiv.Infinitesimal
import Lemma.Nat.NotLt.is.Ge
open Hyperreal Rat Nat Int


abbrev XEq (α : Sort u) := Setoid α

namespace XEq
export Setoid (symm trans)
end XEq

