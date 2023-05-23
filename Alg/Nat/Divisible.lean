import Alg.Nat.Mul.Cmp
import Alg.Nat.Mul.Sub

def dvd (a b: nat) := ∃x, b = a * x

infixl:50 " ∣ " => dvd

theorem dvd.zero (a: nat) : a ∣ nat.zero := ⟨ nat.zero , nat.mul_zero_right.symm ⟩

#print axioms dvd.zero

theorem dvd.by_zero (a: nat) : nat.zero ∣ a -> a = .zero := fun ⟨ _, prf ⟩ => prf

#print axioms dvd.zero

theorem dvd.one (a: nat) : nat.zero.inc ∣ a := ⟨ a , nat.mul_one_left.symm ⟩

#print axioms dvd.one

theorem dvd.id (a: nat) : a ∣ a := ⟨ nat.zero.inc , nat.mul_one_right.symm ⟩

#print axioms dvd.id

theorem dvd.mul_left (a b: nat) : a ∣ a * b := ⟨ b, rfl ⟩

#print axioms dvd.mul_left

theorem dvd.mul_right (a b: nat) : b ∣ a * b := ⟨ a, nat.mul_comm a b ⟩

#print axioms dvd.mul_right

-- theorem dvd.of_mul_com_left (x a b: nat) : x * a ∣ x * b -> a ∣ b := ⟨ b, rfl ⟩

theorem dvd.to_mul_com_left (x a b: nat) : a ∣ b -> x * a ∣ x * b := fun ⟨ y, prfy ⟩ => ⟨ y, by rw [prfy, nat.mul_perm_a_bc_to_ab_c] ⟩

#print axioms dvd.to_mul_com_left

theorem dvd.to_mul_com_right (x a b: nat) : a ∣ b -> a * x ∣ b * x := fun ⟨ y, prfy ⟩ => ⟨ y, by rw [prfy, nat.mul_perm_ab_c_to_ac_b] ⟩

#print axioms dvd.to_mul_com_right

theorem dvd.is_le : a ∣ b -> b ≠ .zero -> a <= b  :=
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

theorem dvd.is_nz : a ∣ b -> b ≠ .zero -> a ≠ .zero :=
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

theorem dvd.not : ¬ (a ∣ b) -> ∀x, b ≠ a * x  := fun not_divis x prf => not_divis ⟨ x, prf ⟩

#print axioms dvd.not

theorem dvd.to_eq : a ∣ b -> b ∣ a -> a = b := by 
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

theorem dvd.trans : a ∣ b -> b ∣ c -> a ∣ c := by 
  intro a_dvd_b b_dvd_c
  have ⟨ x, prfx ⟩ := a_dvd_b
  have ⟨ y, prfy ⟩ := b_dvd_c
  exists x * y
  rw [prfy, prfx]
  rw [nat.mul_assoc]

#print axioms dvd.trans

theorem dvd.to_add : x ∣ a -> x ∣ b -> x ∣ (a + b) := by 
  intro ax bx
  have ⟨ a₀, prfa ⟩ := ax
  have ⟨ b₀, prfb ⟩ := bx
  exists a₀ + b₀
  rw [nat.mul_add_left]
  rw [←prfa, ←prfb]

#print axioms dvd.to_add

theorem dvd.to_mul : x ∣ a -> x ∣ b -> x ∣ (a * b) := by 
  intro ax bx
  have ⟨ a₀, prfa ⟩ := ax
  have ⟨ b₀, prfb ⟩ := bx
  exists a₀ * x * b₀
  rw [nat.mul_perm_a_bc_to_ab_c, nat.mul_perm_a_bc_to_ab_c]
  rw [←prfa]
  rw [←nat.mul_perm_a_bc_to_ab_c]
  rw [←prfb]

#print axioms dvd.to_mul

theorem dvd.to_sub : x ∣ a -> x ∣ b -> x ∣ (a - b) := by 
  intro ax bx
  match x with
  | .zero =>
    have a_eq_zero := ax.by_zero
    rw [a_eq_zero]
    rw [nat.sub_zero_left]
    exact dvd.zero _
  | .inc x =>
  match Compare.dec_lt b a with
  | .isTrue _ =>
    have ⟨ a₀, prfa ⟩ := ax
    have ⟨ b₀, prfb ⟩ := bx
    exists a₀ - b₀
    rw [nat.mul_sub_left]
    rw [prfa, prfb]
    apply @nat.of_le_mul_left_irr x.inc nat.noConfusion
    rw [←prfa, ←prfb]
    apply Or.inl
    assumption
  | .isFalse h =>
    have h := Compare.not_lt_is_le h
    rw [nat.sub_le h]
    exact dvd.zero _

#print axioms dvd.to_sub

theorem dvd.add_cancel_left : x ∣ a -> x ∣ (a + b) -> x ∣ b := by
  intro ax abx
  cases x
  have := abx.by_zero
  have ⟨ _, b_eq_zero ⟩ := nat.add_eq_zero this
  rw [b_eq_zero]
  unfold dvd
  exists nat.zero
  next x => {
    have ⟨ a₀, prfa ⟩ := ax
    have ⟨ ab₀, prfab ⟩ := abx
    exists ab₀ - a₀
    rw [nat.mul_sub_left]
    rw [←prfab, ←prfa]
    rw [nat.sub_add_inv]
    rw [prfa] at prfab
    have : nat.inc x ≠ .zero := nat.noConfusion
    apply nat.of_le_mul_left_irr this
    rw [←prfab]
    apply nat.a_le_a_add_b
  }

#print axioms dvd.add_cancel_left

theorem dvd.add_cancel_right : x ∣ b -> x ∣ (a + b) -> x ∣ a := by
  rw [nat.add_comm]
  apply dvd.add_cancel_left

#print axioms dvd.add_cancel_right
