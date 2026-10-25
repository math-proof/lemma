-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean: instance decls only.
import Def.CerednikDrinfeld_Ribbon
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Class.CerednikDrinfeld_MumfordPeriod

set_option autoImplicit false
noncomputable section
namespace CerednikDrinfeld
namespace Mumford

open ModularCurve MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

instance dartAction : MulAction G 𝒯.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), GraphAction.smul_adj g d.adj⟩
  one_smul d := SimpleGraph.Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d := SimpleGraph.Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))


end Mumford
end CerednikDrinfeld
end
