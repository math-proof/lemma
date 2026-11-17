-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean: instance decls only.

module

public import Def.CerednikDrinfeld_Ribbon
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Class.CerednikDrinfeld_MumfordPeriod

@[expose] public section

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
