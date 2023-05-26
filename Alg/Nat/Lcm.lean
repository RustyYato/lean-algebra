import Alg.Nat.Gcd

def nat.lcm (a b: nat) := a * b / (a.gcd b)

theorem nat.lcm.comm : lcm a b = lcm b a := by
  unfold lcm
  rw [nat.mul_comm a b, nat.gcd.comm a b]

#print axioms nat.lcm.comm

theorem nat.gcd.mul_lcm (a b: nat) : nat.gcd a b * nat.lcm a b = a * b := by
  unfold lcm
  match decEq (gcd a b) .zero with
  | .isTrue h =>
    have ⟨ a_eq_zero, b_eq_zero ⟩  := gcd.zero h
    rw [a_eq_zero, b_eq_zero]
    rfl
  | .isFalse h =>
  have div_def := nat.div_def (a * b) (gcd a b) h
  have gcd_dvd_mul : gcd a b ∣ a * b := by
    apply dvd.trans (nat.gcd.is_dvd a b).left
    apply dvd.mul_left
  rw [gcd_dvd_mul.to_rem_zero h, nat.add_zero_right, nat.mul_comm _ (gcd a b)] at div_def
  exact div_def.symm

#print axioms nat.gcd.mul_lcm

theorem nat.lcm.of_dvd :
  ∀a b x, a ∣ x -> b ∣ x -> lcm a b ∣ x := by
  intro a b x ax bx
  match x with
  | nat.zero => exact dvd.zero _
  | nat.inc x =>
  apply dvd.mul_cancel_com_left (
    nat.gcd.nz a b (Or.inr (bx.nz nat.noConfusion))
  )
  rw [nat.gcd.mul_lcm]
  rw [←nat.gcd.mul_right]
  apply gcd.of_dvd
  have ⟨ y, prf ⟩ := bx
  exists y
  rw [prf]
  apply nat.mul_assoc
  have ⟨ y, prf ⟩ := ax
  exists y
  rw [prf]
  apply nat.mul_perm_a_bc_to_ba_c

#print axioms nat.lcm.of_dvd

theorem nat.lcm.dvd_left { a b } : a ∣ lcm a b := by
  match decEq (gcd a b) .zero with
  | .isTrue h =>
    have ⟨ a_eq_zero, b_eq_zero ⟩  := gcd.zero h
    rw [a_eq_zero, b_eq_zero]
    exact dvd.zero _
  | .isFalse h =>
  apply dvd.mul_cancel_com_left h
  rw [nat.gcd.mul_lcm]
  rw [nat.mul_comm]
  have ⟨ _, ⟨ x, prf ⟩  ⟩  := nat.gcd.is_dvd a b
  exists x
  rw [nat.mul_perm_ab_c_to_a_bc, ←prf]

#print axioms nat.lcm.dvd_left

theorem nat.lcm.dvd_right { a b } : b ∣ lcm a b := by
  rw [nat.lcm.comm]
  exact nat.lcm.dvd_left

#print axioms nat.lcm.dvd_right

theorem nat.lcm.to_dvd :
  ∀{a b x}, lcm a b ∣ x -> a ∣ x ∧ b ∣ x := by
  intro a b x lcm
  apply And.intro
  apply dvd.trans (@nat.lcm.dvd_left a b)
  assumption
  apply dvd.trans (@nat.lcm.dvd_right a b)
  assumption

#print axioms nat.lcm.to_dvd

theorem nat.lcm.is_dvd (a b: nat) : a ∣ lcm a b ∧ b ∣ lcm a b := nat.lcm.to_dvd (dvd.id (lcm a b))

#print axioms nat.lcm.is_dvd
