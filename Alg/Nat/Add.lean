import Alg.Nat

@[simp]
def nat.add (a b: nat) : nat := match a with
  | .zero => b
  | .inc a₀ => .inc (a₀.add b)

#print axioms nat.add

def nat.add_zero_left : a = .zero -> nat.add a b = b := fun _ => match a with | .zero => rfl

#print axioms nat.add_zero_left

def nat.add_zero_right : b = .zero -> nat.add a b = a := fun b_eq_zero => match a with
  | .zero => b_eq_zero
  | .inc a₀ => by
    unfold nat.add
    rw [nat.add_zero_right b_eq_zero]

#print axioms nat.add_zero_right

def nat.add_eq_zero : nat.add a b = .zero -> a = .zero ∧ b = .zero  := fun ab_eq_zero => match a, b with
  | .zero, .zero => ⟨ rfl, rfl ⟩
  | .inc _, _  => by
    unfold nat.add at ab_eq_zero
    contradiction
  | .zero, .inc b₀ => by
    unfold nat.add at ab_eq_zero
    contradiction

#print axioms nat.add_zero_right

def nat.add_inc_left : nat.add (nat.inc a) b = nat.inc (nat.add a b) := rfl

#print axioms nat.add_inc_left

def nat.add_inc_right : nat.add a (nat.inc b) = nat.inc (nat.add a b) := by
  match a with
  | .zero => rfl
  | .inc a₀ =>
    unfold nat.add
    rw [nat.add_inc_right]

#print axioms nat.add_inc_right

def nat.add_comm (a b: nat) : nat.add a b = nat.add b a := by
  match a, b with
  | .zero, .zero => rfl
  | .inc a₀, .zero
  | .zero, .inc b₀ =>
    rw [nat.add_zero_right rfl, nat.add_zero_left rfl]
  | .inc a₀, .inc b₀ => 
    rw [nat.add_inc_left, nat.add_inc_right]
    rw [nat.add_inc_left, nat.add_inc_right]
    rw [nat.add_comm a₀]

#print axioms nat.add_comm

def nat.add_irr : nat.add a b = nat.add a c -> b = c := by
  intro ab_eq_ac
  match a with
  | .zero =>  
    unfold nat.add at ab_eq_ac
    exact ab_eq_ac
  | .inc a₀ =>
    unfold nat.add at ab_eq_ac
    exact nat.add_irr (nat.of_inc_irr ab_eq_ac)

#print axioms nat.add_irr

def nat.add_eq_add : a = c -> b = d -> nat.add a b = nat.add c d := by
  intro a_eq_c b_eq_d
  rw [a_eq_c, b_eq_d]

#print axioms nat.add_eq_add

def nat.add_id_left : nat.add a b = b -> a = .zero := by
  intro ab_eq_b
  match a with
  | .zero => rfl
  | .inc _ => match b with
     | .zero => rw [nat.add_zero_right rfl] at ab_eq_b; contradiction
     | .inc b₀ =>
      rw [nat.add_inc_right] at ab_eq_b
      have ab_eq_b := nat.of_inc_irr ab_eq_b
      apply nat.add_id_left ab_eq_b

#print axioms nat.add_id_left

def nat.add_id_right : nat.add a b = a -> b = .zero := by
  rw [nat.add_comm]
  exact nat.add_id_left

#print axioms nat.add_id_right

theorem nat.add_assoc (a b c: nat) : add a (add b c) = add (add a b) c := by
  match a with
  | nat.zero =>
    rw [nat.add_zero_left rfl, nat.add_zero_left rfl]
  | nat.inc a₀ => 
      repeat rw [nat.add_inc_left]
      rw [nat.add_assoc a₀]

#print axioms nat.add_assoc

theorem nat.add_perm_a_bc_to_ab_c : add a (add b c) = add (add a b) c := by rw [nat.add_assoc]
theorem nat.add_perm_a_bc_to_ba_c : add a (add b c) = add (add b a) c := by rw [nat.add_assoc, nat.add_comm a b]
theorem nat.add_perm_a_bc_to_ac_b : add a (add b c) = add (add a c) b := by rw [nat.add_comm b, nat.add_assoc]
theorem nat.add_perm_a_bc_to_ca_b : add a (add b c) = add (add c a) b := by rw [nat.add_comm b, nat.add_assoc, nat.add_comm a c]
theorem nat.add_perm_a_bc_to_bc_a : add a (add b c) = add (add b c) a := by rw [nat.add_comm]
theorem nat.add_perm_a_bc_to_cb_a : add a (add b c) = add (add c b) a := by rw [nat.add_comm a, nat.add_comm b]

theorem nat.add_perm_a_bc_to_c_ab : add a (add b c) = add c (add a b) := by rw [nat.add_perm_a_bc_to_ca_b, nat.add_assoc]
theorem nat.add_perm_a_bc_to_c_ba : add a (add b c) = add c (add b a) := by rw [nat.add_perm_a_bc_to_cb_a, nat.add_assoc]
theorem nat.add_perm_a_bc_to_b_ac : add a (add b c) = add b (add a c) := by rw [nat.add_perm_a_bc_to_ba_c, nat.add_assoc]
theorem nat.add_perm_a_bc_to_b_ca : add a (add b c) = add b (add c a) := by rw [nat.add_perm_a_bc_to_bc_a, nat.add_assoc]
theorem nat.add_perm_a_bc_to_a_cb : add a (add b c) = add a (add c b) := by rw [nat.add_perm_a_bc_to_ac_b, nat.add_assoc]

theorem nat.add_perm_ab_c_to_c_ab : add (add a b) c = add c (add a b) := by rw [←nat.add_perm_a_bc_to_bc_a]
theorem nat.add_perm_ab_c_to_c_ba : add (add a b) c = add c (add b a) := by rw [←nat.add_perm_a_bc_to_cb_a]
theorem nat.add_perm_ab_c_to_b_ac : add (add a b) c = add b (add a c) := by rw [←nat.add_perm_a_bc_to_ba_c]
theorem nat.add_perm_ab_c_to_b_ca : add (add a b) c = add b (add c a) := by rw [←nat.add_perm_a_bc_to_ca_b]
theorem nat.add_perm_ab_c_to_a_bc : add (add a b) c = add a (add b c) := by rw [←nat.add_perm_a_bc_to_ab_c]
theorem nat.add_perm_ab_c_to_a_cb : add (add a b) c = add a (add c b) := by rw [←nat.add_perm_a_bc_to_ac_b]

theorem nat.add_perm_ab_c_to_ba_c : add (add a b) c = add (add b a) c := by rw [nat.add_perm_ab_c_to_a_bc, nat.add_perm_a_bc_to_ba_c]
theorem nat.add_perm_ab_c_to_ac_b : add (add a b) c = add (add a c) b := by rw [nat.add_perm_ab_c_to_a_bc, nat.add_perm_a_bc_to_ac_b]
theorem nat.add_perm_ab_c_to_ca_b : add (add a b) c = add (add c a) b := by rw [nat.add_perm_ab_c_to_a_bc, nat.add_perm_a_bc_to_ca_b]
theorem nat.add_perm_ab_c_to_bc_a : add (add a b) c = add (add b c) a := by rw [nat.add_perm_ab_c_to_a_bc, nat.add_perm_a_bc_to_bc_a]
theorem nat.add_perm_ab_c_to_cb_a : add (add a b) c = add (add c b) a := by rw [nat.add_perm_ab_c_to_a_bc, nat.add_perm_a_bc_to_cb_a]
