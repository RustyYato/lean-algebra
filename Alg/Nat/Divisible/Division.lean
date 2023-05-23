import Alg.Nat.Divisible
import Alg.Nat.Division

def dvd.to_div_exact {a b : nat} (dvd_a_b: a ∣ b) (a_nz: a ≠ .zero): b = (b / a) * a := by
  have ⟨ x, prf ⟩ := dvd_a_b 
  have ⟨ q , _ ⟩  := nat.from_div_def (a * x) a a_nz x .zero (nat.ne_zero_to_gt_zero a_nz) (by
    rw [nat.mul_comm, nat.add_zero_right])
  rw [←prf] at q
  rw [q, nat.mul_comm] at prf
  exact prf

#print axioms dvd.to_div_exact

def dvd.to_rem_zero {a b : nat} (dvd_a_b: a ∣ b) (a_nz: a ≠ .zero): (b % a) = .zero := by
  have ⟨ x, prf ⟩ := dvd_a_b 
  have ⟨ _ , r ⟩  := nat.from_div_def (a * x) a a_nz x .zero (nat.ne_zero_to_gt_zero a_nz) (by
    rw [nat.mul_comm, nat.add_zero_right])
  rw [←prf] at r
  exact r.symm

#print axioms dvd.to_rem_zero

def dvd.of_rem_zero {a b : nat} (a_nz: a ≠ .zero): (b % a) = .zero -> a ∣ b := by
  intro rem_eq_zero
  rw [nat.div_def b a]
  rw [rem_eq_zero]
  rw [nat.add_zero_right]
  apply dvd.mul_right
  assumption

#print axioms dvd.of_rem_zero

def dvd.of_rem_nz {a b : nat} (a_nz: a ≠ .zero): (b % a) ≠ .zero -> ¬(a ∣ b) := by
  intro rem_nz dvd_a_b
  have := dvd_a_b.to_rem_zero a_nz
  contradiction

#print axioms dvd.of_rem_nz

instance dvd.dec {a b} {a_nz: a ≠ .zero} : Decidable (a ∣ b) := by
  match decEq (b % a) nat.zero with
  | .isTrue rem_eq_zero =>
    apply Decidable.isTrue
    have := dvd.of_rem_zero a_nz rem_eq_zero
    assumption
  | .isFalse rem_nz =>
    apply Decidable.isFalse
    have := dvd.of_rem_nz a_nz rem_nz
    exact this

#print axioms dvd.dec

instance dvd.dec_auto {a b: nat} : Decidable (nat.inc a ∣ b) := 
  @dvd.dec a.inc b nat.noConfusion

#print axioms dvd.dec_auto

theorem dvd.of_rem : ∀a b (_: b ≠ .zero), ∀{{x}} (_: x ∣ a) (_: x ∣ b), x ∣ (a % b) := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    intro x dvd_a _
    rw [nat.remainder.base]
    repeat assumption
  }

  {
    intro a b b_nz a_lt_b prev
    intro x dvd_a dvd_b
    rw [nat.remainder.induct]
    have := prev (dvd.to_sub dvd_a dvd_b) dvd_b
    repeat assumption
  }

#print axioms dvd.of_rem

theorem dvd.rem_cancel_right : ∀a b (_: b ≠ .zero), ∀{{x}} (_: x ∣ b) (_: x ∣ a % b), x ∣ a := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    intro x _ dvd_rem
    rw [nat.remainder.base] at dvd_rem
    exact dvd_rem
    repeat assumption
  }

  {
    intro a b b_nz a_lt_b prev
    intro x dvd_a dvd_rem
    rw [nat.remainder.induct] at dvd_rem
    have := prev dvd_a dvd_rem
    have := dvd.to_add this dvd_a
    rw [nat.add_comm, nat.add_sub_inv] at this
    repeat assumption
  }

#print axioms dvd.rem_cancel_right
