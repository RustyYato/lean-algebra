import Alg.Nat.Add

@[simp]
def nat.mul (a b: nat) : nat := match a with
  | .zero => .zero
  | .inc a₀ => b + nat.mul a₀ b

@[simp]
instance nat.Mul : Mul nat where
  mul := nat.mul

def nat.mul_inc_left : (nat.inc a) * b = b + a * b := rfl

#print axioms nat.mul_inc_left

def nat.mul_zero_left : nat.zero * b = nat.zero := rfl

#print axioms nat.mul_zero_left

def nat.mul_zero_right : a * nat.zero = nat.zero := match a with
  | .zero => rfl
  | .inc a₀ => by
    rw [nat.mul_inc_left, nat.add_zero_left]
    apply nat.mul_zero_right

#print axioms nat.mul_zero_right

def nat.mul_inc_right : a * (nat.inc b) = a + a * b := by
  match a with
  | .zero =>
    rw [nat.mul_zero_left, nat.mul_zero_left, nat.add_zero_left]
  | .inc a₀ =>
    rw [nat.mul_inc_left, nat.mul_inc_left]
    rw [nat.add_inc_left, nat.add_inc_left]
    rw [nat.add_perm_a_bc_to_b_ac]
    apply nat.to_inc_irr
    apply nat.add_eq_add rfl
    apply nat.mul_inc_right

#print axioms nat.mul_inc_right

def nat.mul_one_left : nat.zero.inc * b = b := by
    rw [nat.mul_inc_left, nat.mul_zero_left, nat.add_zero_right]

#print axioms nat.mul_one_left

def nat.mul_one_right : a * nat.zero.inc = a := by
    rw [nat.mul_inc_right, nat.mul_zero_right, nat.add_zero_right]

#print axioms nat.mul_one_right

def nat.mul_id_left : a * b = b -> b ≠ .zero -> a = nat.zero.inc := fun muldef b_ne_zero => match a with
  | .inc .zero => rfl
  | .zero => (b_ne_zero (by
    rw [nat.mul_zero_left] at muldef
    exact muldef.symm
    )).elim
  | .inc (.inc a₀) => by
    rw [nat.mul_inc_left, nat.mul_inc_left] at muldef
    have := nat.add_id_right muldef
    match b with 
    | .inc _ =>
    rw [nat.add_inc_left] at this
    contradiction

#print axioms nat.mul_id_left

def nat.mul_id_right : a * b = a -> a ≠ .zero -> b = nat.zero.inc := fun muldef a_ne_zero => match b with
  | .inc .zero => rfl
  | .zero => (a_ne_zero (by
    rw [nat.mul_zero_right] at muldef
    exact muldef.symm
  )).elim
  | .inc (.inc b₀) => by
    rw [nat.mul_inc_right, nat.mul_inc_right] at muldef
    have := nat.add_id_right muldef
    match a with 
    | .inc _ =>
    rw [nat.add_inc_left] at this
    contradiction

#print axioms nat.mul_id_right

def nat.to_mul_irr { a b c: nat } : a = b -> a * c = b * c := by
  intro a_eq_b
  rw [a_eq_b]

#print axioms nat.to_mul_irr

def nat.of_mul_irr { a b c: nat } : a * c = b * c -> c ≠ .zero -> a = b := fun muldef c_ne_zero => match c with
  | .inc c₀ => by
    match a, b with
    | .zero, .zero => rfl
    | .inc a₀, .inc b₀ =>
      apply nat.to_inc_irr
      rw [nat.mul_inc_left, nat.mul_inc_left] at muldef
      exact nat.of_mul_irr (nat.add_irr muldef) c_ne_zero
    | .inc _, .zero
    | .zero, .inc _ =>
      rw [nat.mul_zero_left, nat.mul_inc_left, nat.add_inc_left] at muldef
      contradiction
    
#print axioms nat.of_mul_irr

def nat.mul_comm (a b: nat) : a * b = b * a := by
  cases a
  rw [nat.mul_zero_left, nat.mul_zero_right]
  rw [nat.mul_inc_left, nat.mul_inc_right]
  apply nat.add_eq_add rfl
  apply nat.mul_comm
    
#print axioms nat.mul_comm

def nat.mul_add_left { a b c: nat } : a * (b + c) = a * b + a * c := by
  cases a
  repeat rw [nat.mul_zero_left]
  rw [nat.add_zero_left]
  repeat rw [nat.mul_inc_left]
  rw [@nat.add_perm_ab_c_to_a_bc]
  rw [@nat.add_perm_ab_c_to_a_bc]
  apply nat.add_eq_add rfl
  rw [@nat.add_perm_a_bc_to_b_ac]
  apply nat.add_eq_add rfl
  apply nat.mul_add_left

#print axioms nat.mul_add_left

def nat.mul_add_right { a b c: nat } : (a + b) * c = a * c + b * c := by
  rw [nat.mul_comm]
  rw [nat.mul_add_left]
  rw [nat.mul_comm c, nat.mul_comm c]

#print axioms nat.mul_add_right

def nat.mul_assoc (a b c: nat) : a * (b * c) = (a * b) * c := by
  cases a
  repeat rw [nat.mul_zero_left]
  repeat rw [nat.mul_inc_left]
  rw [nat.mul_add_right]
  apply nat.add_eq_add rfl
  apply nat.mul_assoc

#print axioms nat.mul_assoc

theorem nat.mul_perm_a_bc_to_ab_c { a b c: nat } : a * (b * c) = (a * b) * c := by rw [nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_ba_c { a b c: nat } : a * (b * c) = (b * a) * c := by rw [nat.mul_assoc, nat.mul_comm a b]
theorem nat.mul_perm_a_bc_to_ac_b { a b c: nat } : a * (b * c) = (a * c) * b := by rw [nat.mul_comm b, nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_ca_b { a b c: nat } : a * (b * c) = (c * a) * b := by rw [nat.mul_comm b, nat.mul_assoc, nat.mul_comm a c]
theorem nat.mul_perm_a_bc_to_bc_a { a b c: nat } : a * (b * c) = (b * c) * a := by rw [nat.mul_comm]
theorem nat.mul_perm_a_bc_to_cb_a { a b c: nat } : a * (b * c) = (c * b) * a := by rw [nat.mul_comm a, nat.mul_comm b]

theorem nat.mul_perm_a_bc_to_c_ab { a b c: nat } : a * (b * c) = c * (a * b) := by rw [nat.mul_perm_a_bc_to_ca_b, nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_c_ba { a b c: nat } : a * (b * c) = c * (b * a) := by rw [nat.mul_perm_a_bc_to_cb_a, nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_b_ac { a b c: nat } : a * (b * c) = b * (a * c) := by rw [nat.mul_perm_a_bc_to_ba_c, nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_b_ca { a b c: nat } : a * (b * c) = b * (c * a) := by rw [nat.mul_perm_a_bc_to_bc_a, nat.mul_assoc]
theorem nat.mul_perm_a_bc_to_a_cb { a b c: nat } : a * (b * c) = a * (c * b) := by rw [nat.mul_perm_a_bc_to_ac_b, nat.mul_assoc]

theorem nat.mul_perm_ab_c_to_c_ab { a b c: nat } : (a * b) * c = c * (a * b) := by rw [←nat.mul_perm_a_bc_to_bc_a]
theorem nat.mul_perm_ab_c_to_c_ba { a b c: nat } : (a * b) * c = c * (b * a) := by rw [←nat.mul_perm_a_bc_to_cb_a]
theorem nat.mul_perm_ab_c_to_b_ac { a b c: nat } : (a * b) * c = b * (a * c) := by rw [←nat.mul_perm_a_bc_to_ba_c]
theorem nat.mul_perm_ab_c_to_b_ca { a b c: nat } : (a * b) * c = b * (c * a) := by rw [←nat.mul_perm_a_bc_to_ca_b]
theorem nat.mul_perm_ab_c_to_a_bc { a b c: nat } : (a * b) * c = a * (b * c) := by rw [←nat.mul_perm_a_bc_to_ab_c]
theorem nat.mul_perm_ab_c_to_a_cb { a b c: nat } : (a * b) * c = a * (c * b) := by rw [←nat.mul_perm_a_bc_to_ac_b]

theorem nat.mul_perm_ab_c_to_ba_c { a b c: nat } : (a * b) * c = (b * a) * c := by rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_perm_a_bc_to_ba_c]
theorem nat.mul_perm_ab_c_to_ac_b { a b c: nat } : (a * b) * c = (a * c) * b := by rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_perm_a_bc_to_ac_b]
theorem nat.mul_perm_ab_c_to_ca_b { a b c: nat } : (a * b) * c = (c * a) * b := by rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_perm_a_bc_to_ca_b]
theorem nat.mul_perm_ab_c_to_bc_a { a b c: nat } : (a * b) * c = (b * c) * a := by rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_perm_a_bc_to_bc_a]
theorem nat.mul_perm_ab_c_to_cb_a { a b c: nat } : (a * b) * c = (c * b) * a := by rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_perm_a_bc_to_cb_a]
