module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem List.ProdAppend.eq.MulProdS
  [Monoid α]
-- given
  (a b : List α) :
-- imply
  (a ++ b).prod = a.prod * b.prod :=
-- proof
  List.prod_append


public theorem List.MulProdS.eq.ProdAppend
  [Monoid α]
  (a b : List α) :
  a.prod * b.prod = (a ++ b).prod :=
  (List.ProdAppend.eq.MulProdS a b).symm


-- created on 2025-06-14
