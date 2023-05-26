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

theorem nat.div_one : ∀x, x / nat.zero.inc = x := by
  intro x
  have := (dvd.one x).to_div_exact nat.noConfusion
  conv => {
    lhs
    rw [←@nat.mul_one_right (_ / _)]
  }
  exact this.symm

theorem nat.mul_div : ∀{a b: nat}, b ≠ .zero -> a * b / b = a := by
  intro a b b_nz
  match b with
  | .inc b =>
  have := (dvd.mul_right a b.inc).to_div_exact nat.noConfusion
  apply nat.of_mul_irr
  exact this.symm
  exact nat.noConfusion

#print axioms nat.zero_div

theorem nat.div_add.helper : ∀{a c}, c ≠ .zero -> ∀b,  c ∣ a -> c ∣ b -> (a + b) / c = a / c + (b / c) := by
  apply divrem.induction
  {
    intro a c c_nz _
    intro b c_dvd_a c_dvd_b
    conv => {
      lhs
      rw [c_dvd_a.to_div_exact c_nz]
      rw [c_dvd_b.to_div_exact c_nz]
    }
    rw [←nat.mul_add_right]
    rw [nat.mul_div]
    assumption
  }

  {
    intro a c c_nz a_ge_c prev
    intro b c_dvd_a c_dvd_b
    rw [nat.divide.induct]
    rw [nat.divide.induct a_ge_c]
    rw [nat.add_inc_left]
    apply nat.to_inc_irr
    have := nat.add_subs a c b nat.zero a_ge_c (nat.zero_le _)
    rw [nat.add_zero_right, nat.sub_zero] at this
    rw [←this]
    apply prev b _ c_dvd_b
    exact dvd.to_sub c_dvd_a (dvd.id _)
    assumption
    apply Compare.le_trans a_ge_c
    apply nat.a_le_a_add_b
    assumption
  }

#print axioms nat.div_add.helper

theorem nat.div_add : ∀{a b c}, c ∣ a -> c ∣ b -> (a + b) / c = a / c + (b / c) := by
  intro a b c
  match c with
  | .inc _ =>
    apply nat.div_add.helper
    exact nat.noConfusion
  | .zero =>
    intro _ _
    repeat rw [nat.div_zero]
    rfl

#print axioms nat.div_add

theorem nat.div_mul_assoc : ∀{a b c}, c ∣ b -> (a * b) / c = a * (b / c) := by
  intro a b c c_dvd_b
  match a with
  | .zero =>
    rw [nat.mul_zero_left, nat.mul_zero_left]
    rw [nat.zero_div]
  | .inc a =>
    rw [nat.mul_inc_left, nat.mul_inc_left]
    rw [nat.div_add]
    apply nat.add_eq_add
    rfl
    apply nat.div_mul_assoc
    repeat assumption
    apply dvd.trans c_dvd_b
    apply dvd.mul_right

#print axioms nat.div_mul_assoc

theorem nat.to_div_com_left : ∀{a b}, b ≠ zero -> ∀x, x ≠ .zero -> a / b = (x * a) / (x * b) := by
  apply divrem.induction
  {
    intro a b b_nz a_lt_b
    intro x x_nz
    match x with 
    | .inc x =>
    have : x.inc * a < x.inc * b := by
      apply nat.to_lt_mul_left_irr
      exact nat.noConfusion
      assumption
    match b with
    | .inc b =>
    rw [nat.divide.base a_lt_b]
    rw [nat.divide.base this]
    rw [nat.mul_inc_left, nat.add_inc_left]
    repeat exact nat.noConfusion
  }
  {
    intro a b b_nz a_ge_b prev
    intro x x_nz
    match x with
    | .inc x =>
      have : x.inc * b <= x.inc * a := by
        apply nat.to_le_mul_left_irr
        assumption
      rw [nat.divide.induct a_ge_b]
      rw [nat.divide.induct this]
      apply nat.to_inc_irr
      rw [←nat.mul_sub_left]
      apply prev
      assumption
      assumption
      match b with
        |.inc b =>
        rw [nat.mul_inc_left, nat.add_inc_left]
        exact nat.noConfusion
      assumption
  }

theorem nat.div_eq_div.helper : ∀{a b}, b ≠ zero -> ∀{c d}, b ∣ a -> d ∣ c -> (a * c) / (b * d) = (a / b) * (c / d) := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    intro c d b_dvd_a _
    rw [nat.divide.base a_lt_b]
    rw [nat.mul_zero_left]
    match a with
    | .zero => rw [nat.mul_zero_left, nat.zero_div]
    | .inc a =>
      have := b_dvd_a.is_le nat.noConfusion
      have := Compare.not_lt_and_le a_lt_b
      contradiction
    assumption
  }

  {
    intro a b b_nz a_ge_b prev
    intro c d b_dvd_a d_dvd_c
    match d with
    | .zero =>
      rw [nat.mul_zero_right, nat.div_zero, nat.div_zero, nat.mul_zero_right]
    | .inc d =>
    rw [nat.divide.induct a_ge_b]
    rw [nat.mul_inc_left]
    rw [←prev (dvd.to_sub b_dvd_a (dvd.id _)) d_dvd_c]
    have : c / d.inc = (b * c) / (b * d.inc) := by
      apply nat.to_div_com_left
      exact nat.noConfusion
      assumption
    rw [this, ←nat.div_add]
    rw [nat.mul_comm b c, nat.mul_comm (a - b) c, nat.mul_sub_left]
    rw [nat.add_sub_inv]
    rw [nat.mul_comm a c]
    apply nat.to_le_mul
    apply Compare.le_id
    assumption
    assumption
    apply d_dvd_c.to_mul_com_left
    apply dvd.trans
    apply d_dvd_c.to_mul_com_left
    apply dvd.to_mul_com_right
    apply dvd.to_sub
    assumption
    apply dvd.id
    assumption
  }
  
#print axioms nat.div_eq_div.helper

theorem nat.div_eq_div : ∀{a b c d}, b ∣ a -> d ∣ c -> (a * c) / (b * d) = (a / b) * (c / d) := by
  intro a b c d b_dvd_a d_dvd_c
  match b with
  | .zero =>
    rw [nat.mul_zero_left, nat.div_zero, nat.div_zero, nat.mul_zero_left]
  | .inc b =>
  apply nat.div_eq_div.helper
  exact nat.noConfusion
  assumption
  assumption
  
#print axioms nat.div_eq_div

theorem nat.div_id : ∀{a}, a ≠ .zero -> a / a = nat.zero.inc := by
  intro a a_nz
  have div_def := (dvd.id a).to_div_exact a_nz
  match h:(a / a) with
  | .zero =>
    rw [h, nat.mul_zero_left] at div_def
    contradiction
  | .inc .zero => rfl
  | .inc (.inc x) =>
    rw [h, nat.mul_inc_left, nat.mul_inc_left] at div_def
    conv at div_def => {
      lhs
      rw [←@nat.add_zero_right a]
    }
    have div_def := nat.add_irr div_def
    match a with
    | .inc a =>
    rw [nat.add_inc_left] at div_def
    contradiction
  
#print axioms nat.div_eq_div
