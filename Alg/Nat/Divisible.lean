import Alg.Nat.Mul.Cmp

def dvd (a b: nat) := ∃x, b = a * x

infixl:30 " | " => dvd

theorem dvd.zero (a: nat) : a | nat.zero := ⟨ nat.zero , nat.mul_zero_right.symm ⟩

#print axioms dvd.zero

theorem dvd.by_zero (a: nat) : nat.zero | a -> a = .zero := fun ⟨ _, prf ⟩ => prf

#print axioms dvd.zero

theorem dvd.one (a: nat) : nat.zero.inc | a := ⟨ a , nat.mul_one_left.symm ⟩

#print axioms dvd.one

theorem dvd.id (a: nat) : a | a := ⟨ nat.zero.inc , nat.mul_one_right.symm ⟩

#print axioms dvd.id

theorem dvd.mul_left (a b: nat) : a | a * b := ⟨ b, rfl ⟩

#print axioms dvd.mul_left

theorem dvd.mul_right (a b: nat) : b | a * b := ⟨ a, nat.mul_comm a b ⟩

#print axioms dvd.mul_right

theorem dvd.is_le : a | b -> b ≠ .zero -> a <= b  :=
  fun ⟨ x, prf ⟩ _ =>
    match b with
    | .inc b₀ => by
      match x with
        | nat.zero =>
          rw [nat.mul_zero_right] at prf
          contradiction
        | nat.inc x₀ =>
          exact (nat.of_le_mul_const_right · (Or.inr (Compare.ord_from_eq prf.symm))) nat.noConfusion

#print axioms dvd.is_le

theorem dvd.is_nz : a | b -> b ≠ .zero -> a ≠ .zero  :=
  fun ⟨ x, prf ⟩ _ =>
    match b with
    | .inc b₀ => by
      match x with
        | nat.zero =>
          rw [nat.mul_zero_right] at prf
          contradiction
        | nat.inc x₀ =>
          match a with
          | .zero => 
            rw [nat.mul_zero_left] at prf
            contradiction
          | .inc a₀ =>
            exact nat.noConfusion

#print axioms dvd.is_nz

theorem dvd.not : ¬ (a | b) -> ∀x, b ≠ a * x  := fun not_divis x prf => not_divis ⟨ x, prf ⟩

#print axioms dvd.not

theorem dvd.to_eq : a | b -> b | a -> a = b := by 
  intro a_dvd_b b_dvd_a
  have ⟨ x, prfx ⟩ := a_dvd_b
  have ⟨ y, prfy ⟩ := b_dvd_a 
  clear a_dvd_b b_dvd_a
  cases a
  rw [nat.mul_zero_left] at prfx
  exact prfx.symm
  rw [prfx] at prfy
  rw [nat.mul_perm_ab_c_to_a_bc] at prfy
  have xy_eq_one := nat.mul_id_right prfy.symm nat.noConfusion
  have ⟨ x_eq_one, y_eq_one ⟩   := nat.mul_eq_one xy_eq_one
  rw [x_eq_one, nat.mul_one_right] at prfx
  exact prfx.symm

#print axioms dvd.to_eq

theorem dvd.trans : a | b -> b | c -> a | c := by 
  intro a_dvd_b b_dvd_c
  have ⟨ x, prfx ⟩ := a_dvd_b
  have ⟨ y, prfy ⟩ := b_dvd_c
  exists x * y
  rw [prfy, prfx]
  rw [nat.mul_assoc]

#print axioms dvd.trans