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

def nat.mul_zero_left : a = nat.zero -> a * b = nat.zero := fun a_eq_zero => match a with | .zero => a_eq_zero

#print axioms nat.mul_zero_left

def nat.mul_zero_right : b = nat.zero -> a * b = nat.zero := fun _ => match b with
  | .zero => match a with
  | .zero => rfl
  | .inc a₀ => by
    rw [nat.mul_inc_left, nat.add_zero_left rfl]
    apply nat.mul_zero_right rfl

#print axioms nat.mul_zero_right

def nat.mul_inc_right : a * (nat.inc b) = a + a * b := by
  match a with
  | .zero =>
    rw [nat.mul_zero_left rfl, nat.mul_zero_left rfl, nat.add_zero_left rfl]
  | .inc a₀ =>
    rw [nat.mul_inc_left, nat.mul_inc_left]
    rw [nat.add_inc_left, nat.add_inc_left]
    rw [nat.add_perm_a_bc_to_b_ac]
    apply nat.to_inc_irr
    apply nat.add_eq_add rfl
    apply nat.mul_inc_right

#print axioms nat.mul_inc_right

def nat.mul_one_left : a = nat.zero.inc -> a * b = b := fun _ => match a with
  | .inc .zero => by
    rw [nat.mul_inc_left, nat.mul_zero_left rfl, nat.add_zero_right rfl]

#print axioms nat.mul_one_left

def nat.mul_one_right : b = nat.zero.inc -> a * b = a := fun _ => match b with
  | .inc .zero => by
    rw [nat.mul_inc_right, nat.mul_zero_right rfl, nat.add_zero_right rfl]

#print axioms nat.mul_one_right

def nat.mul_id_left : a * b = b -> b ≠ .zero -> a = nat.zero.inc := fun muldef b_ne_zero => match a with
  | .inc .zero => rfl
  | .zero => (b_ne_zero (by
    rw [nat.mul_zero_left rfl] at muldef
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
    rw [nat.mul_zero_right rfl] at muldef
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
      rw [nat.mul_zero_left rfl, nat.mul_inc_left, nat.add_inc_left] at muldef
      contradiction
    
#print axioms nat.of_mul_irr
