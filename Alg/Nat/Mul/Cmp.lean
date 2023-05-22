import Alg.Nat.Add.Cmp
import Alg.Nat.Mul
import Alg.Nat.Add
import Alg.Nat.Cmp

theorem nat.zero_lt_mul_inc_inc { a b: nat } : nat.zero < (.inc a) * (.inc b) := by
  rw [nat.mul_inc_left, nat.add_inc_left]
  apply nat.zero_lt_inc

theorem nat.a_le_a_mul_b (a b: nat) : b ≠ .zero -> a <= a * b := by
  intro b_ne_zero
  match b with
  | .inc .zero =>
    rw [nat.mul_one_right]
    apply Compare.le_id
  | .inc (.inc b₀) =>
    rw [nat.mul_inc_right]
    apply nat.to_le_add_const_right
    apply Compare.le_id

#print axioms nat.a_le_a_mul_b

theorem nat.a_le_b_mul_a (a b: nat) : b ≠ .zero -> a <= b * a := by
  rw [nat.mul_comm]
  apply nat.a_le_a_mul_b

#print axioms nat.a_le_b_mul_a

theorem nat.a_lt_a_mul_b (a b: nat) : a ≠ nat.zero -> nat.zero.inc < b -> a < a * b := by
  intro a_ne_one one_lt_b
  match a, b with
  | .inc a₀, .inc (.inc b₀) =>
  rw [nat.mul_inc_right]
  apply nat.a_lt_a_add_b
  apply nat.zero_lt_mul_inc_inc

#print axioms nat.a_lt_a_mul_b

theorem nat.a_lt_b_mul_a (a b: nat) : a ≠ nat.zero -> nat.zero.inc < b -> a < b * a := by
  rw [nat.mul_comm]
  apply nat.a_lt_a_mul_b

#print axioms nat.a_lt_a_mul_b

theorem nat.to_lt_mul_left_irr (a b: nat) : x ≠ .zero -> a < b -> x * a < x * b := by
  intro a_lt_b x_ne_zero
  match a, b with
  | .zero, .inc b₀ =>
    rw [nat.mul_zero_right]
    match x with
    | .inc _ =>
    apply nat.zero_lt_mul_inc_inc
  | .inc a₀, .inc b₀ =>
    rw [nat.mul_inc_right, nat.mul_inc_right]
    apply nat.to_lt_add_left_irr
    apply nat.to_lt_mul_left_irr
    assumption
    assumption

#print axioms nat.to_lt_mul_left_irr

theorem nat.to_le_mul_left_irr (a b: nat) : a <= b -> x * a <= x * b := by
  intro a_le_b
  cases a <;>  cases b
  apply Compare.le_id
  rw [nat.mul_zero_right]
  apply nat.zero_le _
  have := (nat.not_inc_le_zero  _) a_le_b
  contradiction
  rw [nat.mul_inc_right, nat.mul_inc_right]
  apply nat.to_le_add_left_irr
  apply nat.to_le_mul_left_irr
  assumption

#print axioms nat.to_le_mul_left_irr

theorem nat.of_lt_mul_left_irr : x ≠ nat.zero -> ∀{a b: nat}, x * a < x * b -> a < b := by
  intro x_ne_zero a b a_lt_b
  match a, b with
  | .zero, .zero => rw [nat.mul_zero_right] at a_lt_b; contradiction
  | .zero, .inc b₀ => apply nat.zero_lt_inc
  | .inc a₀, .zero =>
    rw [nat.mul_zero_right] at a_lt_b
    match x with
    | .inc x₀ =>
    rw [nat.mul_inc_left, nat.add_inc_left] at a_lt_b
    have := nat.not_lt_zero _ a_lt_b
    contradiction
  | .inc a₀, .inc b₀ =>
    apply nat.to_lt_inc_irr
    rw [nat.mul_inc_right, nat.mul_inc_right] at a_lt_b
    have := nat.of_lt_add_left_irr a_lt_b
    apply nat.of_lt_mul_left_irr x_ne_zero
    assumption

#print axioms nat.of_lt_mul_left_irr

theorem nat.of_le_mul_left_irr : x ≠ .zero -> ∀{a b: nat}, x * a <= x * b -> a <= b := by
  intro x_ne_zero a b a_lt_b
  match x with
  | .inc x₀ =>
  cases a <;> cases b
  apply Compare.le_id
  apply nat.zero_le _
  rw [nat.mul_zero_right] at a_lt_b
  have := (Compare.not_lt_and_le _ _ · a_lt_b) (@nat.zero_lt_mul_inc_inc x₀ _)
  contradiction
  apply nat.to_le_inc_irr
  rw [nat.mul_inc_right, nat.mul_inc_right] at a_lt_b
  apply nat.of_le_mul_left_irr x_ne_zero
  exact nat.of_le_add_left_irr a_lt_b

#print axioms nat.of_le_mul_left_irr

theorem nat.to_lt_mul_right_irr (a b: nat) : x ≠ .zero -> a < b -> a * x < b * x := by
  rw [nat.mul_comm, nat.mul_comm b]
  apply nat.to_lt_mul_left_irr

#print axioms nat.to_lt_mul_right_irr

theorem nat.to_le_mul_right_irr (a b: nat) : a <= b -> a * x <= b * x := by
  rw [nat.mul_comm, nat.mul_comm b]
  apply nat.to_le_mul_left_irr

#print axioms nat.to_le_mul_right_irr

theorem nat.of_lt_mul_right_irr : x ≠ nat.zero -> ∀{a b: nat}, a * x < b * x -> a < b := by
  intro x_ne_zero a b
  rw [nat.mul_comm, nat.mul_comm b]
  apply nat.of_lt_mul_left_irr x_ne_zero

#print axioms nat.of_lt_mul_right_irr

theorem nat.of_le_mul_right_irr : x ≠ .zero -> ∀{a b: nat}, a * x <= b * x -> a <= b := by
  intro x_ne_zero a b
  rw [nat.mul_comm, nat.mul_comm b]
  apply nat.of_le_mul_left_irr x_ne_zero

#print axioms nat.of_le_mul_right_irr

theorem nat.to_lt_mul_const_left : x ≠ nat.zero -> ∀{a b}, a < b -> a < x * b := by
  intro x_ne_zero a b a_lt_b
  cases b <;> cases a
  contradiction
  contradiction
  match x with
  | .inc x₀ =>
    apply nat.zero_lt_mul_inc_inc
  have a_lt_b := nat.of_lt_inc_irr a_lt_b
  have := nat.to_lt_mul_const_left x_ne_zero a_lt_b
  match x with
  | .inc x₀ =>
    rw [nat.mul_inc_right, nat.add_inc_left]
    apply nat.to_lt_inc_irr
    apply Compare.lt_le_trans this
    apply nat.a_le_b_add_a

#print axioms nat.to_lt_mul_const_left

theorem nat.to_lt_mul_const_right : x ≠ nat.zero -> ∀{a b}, a < b -> a < b * x := by
  intro x_ne_zero a b
  rw [nat.mul_comm]
  apply nat.to_lt_mul_const_left x_ne_zero

#print axioms nat.to_lt_mul_const_right

theorem nat.to_le_mul_const_left : x ≠ .zero -> ∀{a b: nat}, a <= b -> a <= x * b := by
  intro x_ne_zero a b a_le_b
  match a, b with
  | .zero, .zero =>
    rw [nat.mul_zero_right]
    apply Compare.le_id
  | .zero, .inc b₀ =>
    apply nat.zero_le
  | .inc a₀, .inc b₀ =>
    have a_lt_b := nat.of_le_inc_irr a_le_b
    have := nat.to_le_mul_const_left x_ne_zero a_lt_b
    match x with
    | .inc x₀ =>
    rw [nat.mul_inc_right, nat.add_inc_left]
    apply nat.to_le_inc_irr
    apply Compare.le_trans this
    apply nat.a_le_b_add_a

#print axioms nat.to_le_mul_const_left

theorem nat.to_le_mul_const_right : x ≠ .zero -> ∀{a b: nat}, a <= b -> a <= b * x := by
  intro x_ne_zero a b
  rw [nat.mul_comm]
  apply nat.to_le_mul_const_left x_ne_zero

#print axioms nat.to_le_mul_const_right

theorem nat.of_le_mul_const_right {a b c: nat} : b ≠ .zero -> a * b <= c -> a <= c := by
  intro b_ne_zero mul_le
  match c with
  | .zero =>
    have := nat.le_zero mul_le
    match nat.mul_eq_zero this with
    | .inl a_eq_zero => rw [a_eq_zero]; apply Compare.le_id
    | .inr b_eq_zero => contradiction
  | .inc c₀ =>
    match a with
    | .zero => exact nat.zero_le _
    | .inc a₀ =>
      apply nat.to_le_inc_irr
      rw [nat.mul_inc_left] at mul_le
      have := nat.a_lt_b_add_a (a₀ * b) b (nat.ne_zero_to_gt_zero b_ne_zero)
      have := Compare.lt_le_trans this mul_le
      have := nat.lt_inc_to_le this
      apply nat.of_le_mul_const_right b_ne_zero
      assumption

#print axioms nat.of_le_mul_const_right

theorem nat.of_lt_mul_const_right {a b c: nat} :b ≠ .zero -> a * b < c -> a < c := by
  intro b_ne_zero mul_le
  match c with
  | .zero =>
    have := (nat.not_lt_zero _) mul_le
    contradiction
  | .inc c₀ =>
    apply nat.le_to_lt_inc
    apply nat.of_le_mul_const_right b_ne_zero (nat.lt_inc_to_le mul_le)

#print axioms nat.of_lt_mul_const_right

theorem nat.of_le_mul_const_left {a b c: nat} : a ≠ .zero -> a * b <= c -> b <= c := by
  rw [nat.mul_comm]
  exact nat.of_le_mul_const_right

#print axioms nat.of_le_mul_const_left

theorem nat.of_lt_mul_const_left {a b c: nat} : a ≠ .zero -> a * b < c -> b < c := by
  rw [nat.mul_comm]
  exact nat.of_lt_mul_const_right

#print axioms nat.of_lt_mul_const_left

theorem nat.to_le_mul {a b c d: nat} : a <= c -> b <= d -> a * b <= c * d := by
  intro a_le_c b_le_d
  match a, c with
  | .zero, .zero =>
    rw [nat.mul_zero_left, nat.mul_zero_left]
    apply Compare.le_id
  | .zero, .inc c₀ =>
    rw [nat.mul_zero_left]
    apply nat.zero_le
  | .inc a₀, .inc c₀ =>
    rw [nat.mul_inc_left, nat.mul_inc_left]
    apply nat.to_le_add
    assumption
    apply nat.to_le_mul
    exact nat.of_le_inc_irr a_le_c
    assumption

#print axioms nat.to_le_mul

theorem nat.to_lt_mul {a b c d: nat} : a < c -> b < d -> a * b < c * d := by
  intro a_lt_c b_lt_d
  match a, c with
  | .zero, .inc c₀ =>
    rw [nat.mul_zero_left]
    have := nat.gt_zero b_lt_d    
    match d with
    | .inc d₀ =>
    apply nat.zero_lt_mul_inc_inc
  | .inc a₀, .inc c₀ =>
    rw [nat.mul_inc_left, nat.mul_inc_left]
    apply nat.to_lt_add
    assumption
    apply nat.to_lt_mul
    exact nat.of_lt_inc_irr a_lt_c
    assumption

#print axioms nat.to_lt_mul
