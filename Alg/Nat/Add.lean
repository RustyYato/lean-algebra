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

def nat.add_comm : nat.add a b = nat.add b a := by
  match a, b with
  | .zero, .zero => rfl
  | .inc a₀, .zero
  | .zero, .inc b₀ =>
    rw [nat.add_zero_right rfl, nat.add_zero_left rfl]
  | .inc a₀, .inc b₀ => 
    rw [nat.add_inc_left, nat.add_inc_right]
    rw [nat.add_inc_left, nat.add_inc_right]
    rw [nat.add_comm]

#print axioms nat.add_comm

def nat.add_irr : nat.add a b = nat.add a c -> b = c := by
  intro ab_eq_ac
  match a with
  | .zero =>  
    unfold nat.add at ab_eq_ac
    exact ab_eq_ac
  | .inc a₀ =>
    unfold nat.add at ab_eq_ac
    exact nat.add_irr (nat.inc_irr ab_eq_ac)

#print axioms nat.add_irr
