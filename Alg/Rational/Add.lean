import Alg.Rational.Equiv
import Alg.Nat.Mul

def rational.add (a b: rational): rational := 
  rational.mk (a.top * b.bot + a.bot * b.top) (a.bot * b.bot) (by
    intro bot_is_zero
    have := a.bot_nz
    have := b.bot_nz
    cases nat.mul_eq_zero bot_is_zero <;> contradiction)

#print axioms rational.add

instance rational.Add: Add rational where
  add := rational.add

def rational.zero := rational.mk nat.zero nat.zero.inc nat.noConfusion

def rational.add_comm (a b: rational):
  a + b ≈ b + a := by
  unfold HAdd.hAdd instHAdd Add.add Add rational.add
  apply rational.equiv.of_prop
  simp
  rw [nat.mul_comm b.bot a.bot]
  apply nat.to_mul_irr
  rw [nat.add_comm]
  rw [nat.mul_comm b.bot]
  rw [nat.mul_comm b.top]

#print axioms rational.add_comm

def rational.add_eq (a b: rational):
  a ≈ c ->
  b ≈ d ->
  a + b ≈ c + d := by
  intro a_eq_c b_eq_d
  unfold HAdd.hAdd instHAdd Add.add Add rational.add
  apply rational.equiv.of_prop
  simp
  rw [
    nat.mul_add_right, nat.mul_add_right,
    nat.mul_perm_ab_c_to_a_bc,
    nat.mul_comm b.bot,
    nat.mul_perm_ab_c_to_a_bc,
    nat.mul_perm_a_bc_to_ab_c,
    a_eq_c,
    @nat.mul_perm_ab_c_to_a_bc _ b.top,
    @nat.mul_perm_a_bc_to_ac_b b.top,
    b_eq_d,
    @nat.mul_perm_a_bc_to_c_ab a.bot,
    @nat.mul_perm_a_bc_to_b_ac a.bot,
    @nat.mul_perm_a_bc_to_ab_c c.bot,

    @nat.mul_perm_ab_c_to_a_cb c.top,
    @nat.mul_perm_ab_c_to_a_cb d.bot,
    @nat.mul_perm_a_bc_to_ab_c c.top]

#print axioms rational.add_eq

def rational._add_zero_left (a: rational):
  rational.zero + a = a := by
  unfold zero
  unfold HAdd.hAdd instHAdd Add.add Add rational.add
  simp
  congr
  rw [nat.mul_one_left, nat.mul_zero_left, nat.add_zero_left]
  rw [nat.mul_one_left]
 
#print axioms rational._add_zero_left

def rational._add_zero_right (a: rational):
  a + rational.zero = a := by
  unfold zero
  unfold HAdd.hAdd instHAdd Add.add Add rational.add
  simp
  congr
  rw [nat.mul_one_right, nat.mul_zero_right, nat.add_zero_right]
  rw [nat.mul_one_right]
 
#print axioms rational._add_zero_left

def rational.add_zero_left (a b: rational):
  a ≈ rational.zero -> a + b ≈ b := by
  intro a_eq_zero
  conv => {
    rhs
    rw [←rational._add_zero_left b]
  }
  apply rational.add_eq
  assumption
  rfl
  
#print axioms rational.add_zero_left

def rational.add_zero_right (a b: rational):
  b ≈ rational.zero -> a + b ≈ a := by
  intro a_eq_zero
  conv => {
    rhs
    rw [←rational._add_zero_right a]
  }
  apply rational.add_eq
  rfl
  assumption
  
#print axioms rational.add_zero_right
