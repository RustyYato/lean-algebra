import Alg.Nat.Add
import Alg.Nat.Cmp

theorem nat.a_le_a_add_b (a b: nat) : a <= a + b := by
  cases a
  exact nat.zero_le _
  apply nat.to_le_inc_irr
  apply nat.a_le_a_add_b

#print axioms nat.a_le_a_add_b

theorem nat.a_le_b_add_a (a b: nat) : a <= b + a := by
  rw [nat.add_comm]
  apply nat.a_le_a_add_b

#print axioms nat.a_le_b_add_a

theorem nat.a_lt_a_add_b (a b: nat) : nat.zero < b -> a < a + b := by
  intro zero_lt_b
  cases a
  exact zero_lt_b
  apply nat.to_lt_inc_irr
  apply nat.a_lt_a_add_b
  assumption

#print axioms nat.a_lt_a_add_b

theorem nat.a_lt_b_add_a (a b: nat) : nat.zero < b -> a < b + a := by
  rw [nat.add_comm]
  apply nat.a_lt_a_add_b

#print axioms nat.a_lt_a_add_b

theorem nat.to_lt_add_left_irr (a b: nat) : a < b -> x + a < x + b := by
  intro a_lt_b
  cases x
  exact a_lt_b
  rw [nat.add_inc_left, nat.add_inc_left]
  apply nat.to_lt_inc_irr
  apply nat.to_lt_add_left_irr
  assumption

#print axioms nat.to_lt_add_left_irr

theorem nat.to_le_add_left_irr (a b: nat) : a <= b -> x + a <= x + b := by
  intro a_le_b
  cases x
  exact a_le_b
  rw [nat.add_inc_left, nat.add_inc_left]
  apply nat.to_le_inc_irr
  apply nat.to_le_add_left_irr
  assumption

#print axioms nat.to_le_add_left_irr

theorem nat.of_lt_add_left_irr (a b: nat) : x + a < x + b -> a < b := by
  intro a_lt_b
  cases x
  exact a_lt_b
  rw [nat.add_inc_left, nat.add_inc_left] at a_lt_b
  have a_lt_b := nat.of_lt_inc_irr a_lt_b
  exact nat.of_lt_add_left_irr _ _ a_lt_b

#print axioms nat.of_lt_add_left_irr

theorem nat.of_le_add_left_irr {a b: nat} : x + a <= x + b -> a <= b := by
  intro a_lt_b
  cases x
  exact a_lt_b
  rw [nat.add_inc_left, nat.add_inc_left] at a_lt_b
  have a_lt_b := nat.of_le_inc_irr a_lt_b
  exact nat.of_le_add_left_irr a_lt_b

#print axioms nat.of_le_add_left_irr

theorem nat.to_lt_add_right_irr (a b: nat) : a < b -> x + a < x + b := by
  rw [nat.add_comm, nat.add_comm]
  apply nat.to_lt_add_left_irr

#print axioms nat.to_lt_add_right_irr

theorem nat.to_le_add_right_irr (a b: nat) : a <= b -> x + a <= x + b := by
  rw [nat.add_comm, nat.add_comm]
  apply nat.to_le_add_left_irr

#print axioms nat.to_le_add_right_irr

theorem nat.of_lt_add_right_irr (a b: nat) : x + a < x + b -> a < b := by
  rw [nat.add_comm, nat.add_comm]
  apply nat.of_lt_add_left_irr

#print axioms nat.of_lt_add_right_irr

theorem nat.of_le_add_right_irr (a b: nat) : x + a <= x + b -> a <= b := by
  rw [nat.add_comm, nat.add_comm]
  apply nat.of_le_add_left_irr

#print axioms nat.of_le_add_right_irr

theorem nat.to_lt_add_const_left (a b: nat) : a < b -> a < x + b := by
  match x with
  | .zero => exact id
  | .inc x₀ => 
    intro a_le_b
    apply Compare.lt_trans a_le_b
    apply nat.a_lt_b_add_a
    rfl

#print axioms nat.to_lt_add_const_left

theorem nat.to_lt_add_const_right (a b: nat) : a < b -> a < b + x := by
  rw [nat.add_comm]
  apply nat.to_lt_add_const_left

#print axioms nat.to_lt_add_const_right

theorem nat.to_le_add_const_left (a b x: nat) : a <= b -> a <= x + b := by
  match x with
  | .zero => exact id
  | .inc x₀ => 
    intro a_le_b
    apply Compare.le_trans a_le_b
    apply nat.a_le_b_add_a

#print axioms nat.to_le_add_const_left

theorem nat.to_le_add_const_right (a b x: nat) : a <= b -> a <= b + x := by
  rw [nat.add_comm]
  apply nat.to_le_add_const_left

#print axioms nat.to_le_add_const_right

theorem nat.of_le_add_const_right {a b c: nat} : a + b <= c -> a <= c := by
  intro add_le
  match c with
  | .zero =>
    have := nat.le_zero add_le
    have ⟨ a_eq_zero, _ ⟩  := nat.add_eq_zero this
    apply Or.inr
    exact Compare.ord_from_eq a_eq_zero
  | .inc c₀ =>
    match a with
    | .zero => exact nat.zero_le _
    | .inc a₀ =>
      apply nat.to_le_inc_irr
      rw  [nat.add_inc_left] at add_le
      apply nat.of_le_add_const_right
      exact nat.of_le_inc_irr add_le

#print axioms nat.of_le_add_const_right

theorem nat.of_lt_add_const_right {a b c: nat} : a + b < c -> a < c := by
  intro add_lt
  match c with
  | .zero =>
    have := nat.not_lt_zero (a + b)
    contradiction
  | .inc c₀ =>
    match a with
    | .zero => exact nat.zero_lt_inc _
    | .inc a₀ =>
      apply nat.to_lt_inc_irr
      rw  [nat.add_inc_left] at add_lt
      apply nat.of_lt_add_const_right
      exact nat.of_lt_inc_irr add_lt

#print axioms nat.of_lt_add_const_right

theorem nat.of_le_add_const_left {a b c: nat} : a + b <= c -> b <= c := by
  rw [nat.add_comm]
  exact nat.of_le_add_const_right

#print axioms nat.of_le_add_const_left

theorem nat.of_lt_add_const_left {a b c: nat} : a + b < c -> b < c := by
  rw [nat.add_comm]
  exact nat.of_lt_add_const_right

#print axioms nat.of_lt_add_const_left

theorem nat.to_le_add {a b c d: nat} : a <= c -> b <= d -> a + b <= c + d := by
  intro a_le_c b_le_d
  match a, c with
  | .zero, .zero =>
    exact b_le_d
  | .zero, .inc c₀ =>
    rw [nat.add_zero_left]
    have := nat.a_le_b_add_a b (inc c₀)
    apply Compare.le_trans this
    apply nat.to_le_add_left_irr
    assumption
  | .inc a₀, .zero =>
    have := nat.not_inc_le_zero a₀
    contradiction
  | .inc a₀, .inc b₀ =>
    rw [nat.add_inc_left, nat.add_inc_left]
    apply nat.to_le_inc_irr
    apply nat.to_le_add
    exact a_le_c
    exact b_le_d

#print axioms nat.to_le_add

theorem nat.to_lt_le_add {a b c d: nat} : a < c -> b <= d -> a + b < c + d := by
  intro a_le_c b_le_d
  match a, c with
  | .zero, .zero => contradiction
  | .zero, .inc c₀ =>
    rw [nat.add_zero_left]
    rw [nat.add_inc_left]
    apply nat.le_to_lt_inc
    apply Compare.le_trans b_le_d
    apply nat.a_le_b_add_a
  | .inc a₀, .zero => contradiction
  | .inc a₀, .inc c₀ =>
    rw [nat.add_inc_left, nat.add_inc_left]
    apply nat.to_lt_inc_irr
    apply nat.to_lt_le_add
    assumption
    assumption

#print axioms nat.to_lt_le_add

theorem nat.to_le_lt_add {a b c d: nat} : a <= c -> b < d -> a + b < c + d := by
  intro a_le_c b_le_d
  rw [nat.add_comm a, nat.add_comm c]
  apply nat.to_lt_le_add <;> assumption

#print axioms nat.to_le_lt_add

theorem nat.to_lt_add {a b c d: nat} : a < c -> b < d -> a + b < c + d := by
  intro a_lt_c b_lt_d
  apply nat.to_lt_le_add
  assumption
  apply Or.inl
  assumption

#print axioms nat.to_lt_add
