import Alg.Nat

structure rational where
  top: nat
  bot: nat
  bot_nz: bot ≠ .zero

#print axioms rational
