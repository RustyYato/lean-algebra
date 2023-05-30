import Alg.Rational
import Alg.Nat.Mul
import Alg.Nat.Cmp

def rational.equiv (a b: rational) :=
  a.top * b.bot = b.top * a.bot

instance rational.HasEquiv : HasEquiv rational where
  Equiv := rational.equiv

instance rational.Equiv : Equivalence rational.equiv where
  refl := fun x => rfl
  symm := by
    intro x y eq_x_y
    exact eq_x_y.symm
  trans := by
    intro x y z eq_x_y eq_y_z
    unfold equiv at *
    apply nat.of_mul_irr _ y.bot_nz
    rw [nat.mul_perm_ab_c_to_ac_b]
    rw [nat.to_mul_irr eq_x_y]
    rw [nat.mul_perm_ab_c_to_ac_b]
    rw [@nat.mul_perm_ab_c_to_ac_b _ x.bot]
    apply nat.to_mul_irr
    assumption

instance rational.Setoid : Setoid rational where
    r := rational.equiv
    iseqv := rational.Equiv

instance rational.dec_equiv (a b: rational) : Decidable (a ≈ b) := by
  apply Compare.dec_eq

#eval rational.mk nat.zero.inc nat.zero.inc.inc nat.noConfusion ≈
      rational.mk nat.zero.inc.inc nat.zero.inc.inc.inc.inc nat.noConfusion

def rational.equiv.to_prop {a b: rational} (x: a ≈ b): a.top * b.bot = b.top * a.bot := x

def rational.equiv.of_prop {a b: rational} (x: a.top * b.bot = b.top * a.bot): a ≈ b := x

#print axioms rational.equiv.to_prop
