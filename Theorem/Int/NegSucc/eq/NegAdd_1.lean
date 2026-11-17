module

public import Theorem.Int.NegSucc.eq.NegCoeAdd_1

public section

open Int


public theorem Int.NegSucc.eq.NegAdd_1
  {n : ℕ} :
-- imply
  Int.negSucc n = -(n + 1) :=
-- proof
  NegSucc.eq.NegCoeAdd_1


-- created on 2025-03-27
