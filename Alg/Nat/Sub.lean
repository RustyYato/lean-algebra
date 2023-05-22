import Alg.Nat
import Alg.Nat.Add.Cmp

def nat.sub (a b: nat) := match b with
  | .zero => a
  | .inc b₀ => match a with
    | .zero => .zero
    | .inc a₀ => a₀.sub b₀

instance nat.Sub : Sub nat where
  sub := nat.sub

theorem nat.sub_id : a - a = nat.zero := match a with
   | .zero => rfl
   | .inc a₀ => a₀.sub_id

#print axioms nat.sub_id

theorem nat.sub_le : a <= b -> a - b = nat.zero := fun a_le_b => match a with
  | .zero => match b with
    | .zero => rfl
    | .inc _ => rfl
  | .inc a₀ => match b with
    | .inc _ => a₀.sub_le a_le_b

#print axioms nat.sub_le

theorem nat.sub_zero { a: nat } : a - nat.zero = a := by
  cases a <;> rfl

#print axioms nat.sub_zero

theorem nat.sub_inc { a b: nat } : inc a - inc b = a - b := by
  cases a <;> rfl

#print axioms nat.sub_inc

theorem nat.sub_inc_left { a b: nat } : b <= a -> (inc a) - b = inc (a - b) := by
  intro b_le_a
  cases a
  have b_eq_zero := nat.le_zero b_le_a
  rw [b_eq_zero]
  rw [nat.sub_zero, nat.sub_zero]
  match b with
  | .zero => 
    rw [nat.sub_zero]
    rfl
  | .inc b₀ =>
    rw [nat.sub_inc, nat.sub_inc]
    apply nat.sub_inc_left
    assumption

#print axioms nat.sub_inc_left

theorem nat.add_to_sub { a b c: nat } : a + b = c -> a = c - b ∧ b <= c := fun ab_eq_c => by
  cases b
  rw [nat.add_zero_right] at ab_eq_c
  rw [nat.sub_zero]
  exact ⟨ ab_eq_c, nat.zero_le _ ⟩
  rw [nat.add_inc_right] at ab_eq_c
  cases c
  contradiction
  rw [nat.sub_inc]
  apply nat.add_to_sub
  exact nat.of_inc_irr ab_eq_c

#print axioms nat.add_to_sub

theorem nat.sub_to_add { a b c: nat } : a = c - b -> b <= c -> a + b = c := by
  intro a_eq_cb b_le_c
  cases b
  rw [nat.add_zero_right]
  rw [nat.sub_zero] at a_eq_cb
  assumption
  rw [nat.add_inc_right]
  cases c
  have := (nat.not_inc_le_zero _) b_le_c
  contradiction
  apply nat.to_inc_irr
  apply nat.sub_to_add
  rw [nat.sub_inc] at a_eq_cb
  assumption
  exact nat.of_le_inc_irr b_le_c

#print axioms nat.sub_to_add

theorem nat.sub_add_inv { a b: nat } : (a + b) - a = b := by
  cases a
  rw [nat.add_zero_left, nat.sub_zero]
  rw [nat.add_inc_left, nat.sub_inc]
  apply nat.sub_add_inv

#print axioms nat.sub_add_inv

theorem nat.add_sub_inv { a b: nat } : a <= b -> a + (b - a) = b := by
  intro a_le_b
  cases b
  match a with
    | .zero => rfl
  cases a
  rw [nat.add_zero_left, nat.sub_zero]
  rw [nat.sub_inc, nat.add_inc_left]
  apply nat.to_inc_irr
  apply nat.add_sub_inv
  assumption

#print axioms nat.add_sub_inv

theorem nat.sub_is_le (a b: nat) : a - b <= a := by
  cases b
  rw [nat.sub_zero]
  apply Compare.le_id
  cases a
  rw [nat.sub_le (nat.zero_le _)]
  apply Compare.le_id
  rw [nat.sub_inc]
  apply Compare.le_trans _ (nat.le_inc _)
  apply nat.sub_is_le

#print axioms nat.sub_is_le

theorem nat.sub_is_lt (a b: nat) : nat.zero < b -> b <= a -> a - b < a := by
  intro zero_lt_b b_le_a
  match b with
  | .inc .zero =>
    cases a
    have := nat.not_inc_le_zero .zero
    contradiction
    rw [nat.sub_inc, nat.sub_zero]
    apply nat.lt_inc
  | .inc (.inc b₀) =>
  cases a
  have := nat.not_inc_le_zero b₀.inc
  contradiction
  rw [nat.sub_inc]
  apply Compare.lt_le_trans _ (nat.le_inc _)
  apply nat.sub_is_lt
  apply nat.zero_lt_inc
  exact nat.of_le_inc_irr b_le_a

#print axioms nat.sub_is_lt

theorem nat.sub_com_left (a b c: nat) : (a + b) - (a + c) = b - c := by
  cases a
  rfl
  rw [nat.add_inc_left, nat.add_inc_left]
  rw [nat.sub_inc]
  apply nat.sub_com_left

#print axioms nat.sub_com_left

theorem nat.sub_com_right (a b c: nat) : (a + b) - (c + b) = a - c := by
  rw [nat.add_comm, nat.add_comm c]
  apply nat.sub_com_left

#print axioms nat.sub_com_right
