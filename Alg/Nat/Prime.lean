import Alg.Nat.Divisible.Division

def nat.prime (n: nat) := n ≠ nat.zero.inc ∧ ∀x, (
  ¬ x ∣ n ∨ x = n ∨ x = nat.zero.inc
)

def nat.composite (n: nat) := n = nat.zero.inc ∨ ∃x, x ∣ n ∧ x ≠ n ∧ x ≠ nat.zero.inc

def smallest_factor_from (fuel x n: nat): n < fuel + x -> x <= n -> x ≠ .zero -> nat := by
  intro n_lt_fuel_add_x x_le_n x_nz
  match fuel with
  | .zero =>
    rw [nat.add_zero_left] at n_lt_fuel_add_x
    have := Compare.not_lt_and_le n_lt_fuel_add_x x_le_n
    contradiction
  | .inc fuel =>
    match @dvd.dec x n x_nz with
    | .isTrue _ => exact x
    | .isFalse h =>
      apply smallest_factor_from fuel x.inc n
      rw [nat.add_inc_right, ←nat.add_inc_left]
      assumption
      match x_le_n with
      | .inr x_eq_n =>
        rw [Compare.ord_to_eq x_eq_n] at h
        have := dvd.id n
        contradiction
      | .inl h =>
        apply nat.lt_inc_to_le
        exact h
      exact nat.noConfusion

#print axioms smallest_factor_from

def nat.smallest_factor (n: nat) : nat :=
  match n with
  | .zero => .zero
  | .inc .zero => .inc .zero
  | .inc (.inc n) =>
    smallest_factor_from n.inc nat.zero.inc.inc n.inc.inc (by
      rw [nat.add_inc_right, nat.add_inc_right, ←nat.add_inc_left, nat.add_zero_right]
      apply nat.le_to_lt_inc
      apply Compare.le_id) (by
      apply nat.to_le_inc_irr
      apply nat.to_le_inc_irr
      apply nat.zero_le) nat.noConfusion

#print axioms nat.smallest_factor

example : nat.zero.inc.inc.inc.inc.inc.inc.smallest_factor = nat.zero.inc.inc := by decide
example : nat.zero.inc.inc.inc.inc.inc.inc.inc.inc.inc.smallest_factor = nat.zero.inc.inc.inc := by decide

theorem smallest_factor_from.prf (n: nat) :
  ∀fuel x h₀ h₁ h₂, ∀y, x <= y -> y ∣ n -> smallest_factor_from fuel x n h₀ h₁ h₂ <= y
 := by
  intro fuel x h₀ h₁ h₂ y x_le_y y_dvd_n
  unfold smallest_factor_from
  match fuel with
  | .zero =>
    have := Compare.not_lt_and_le h₀
    contradiction
  | .inc fuel =>
    simp
    cases h:dvd.dec <;> simp
    {
      apply smallest_factor_from.prf n fuel x.inc _ _ nat.noConfusion y
      {
        match y with
        | .zero =>
          match x with
          | .zero =>
          contradiction
        | .inc y =>
          apply nat.to_le_inc_irr
          apply nat.lt_inc_to_le
          match x_le_y with
          | .inl h => exact h
          | .inr h₀ =>
            match x with
            | .zero => apply nat.zero_lt_inc
            | .inc x =>
            rw [←Compare.ord_to_eq h₀] at y_dvd_n
            contradiction
      }
      assumption
    }
    assumption

#print axioms smallest_factor_from.prf

theorem smallest_factor_from.ge_start (n: nat) :
  ∀fuel x h₀ h₁ h₂, x <= smallest_factor_from fuel x n h₀ h₁ h₂
 := by
  intro fuel x h₀ h₁ h₂
  unfold smallest_factor_from
  match fuel with
  | .zero =>
    have := Compare.not_lt_and_le h₀
    contradiction
  | .inc fuel =>
    simp
    cases h:dvd.dec <;> simp
    {
      apply Compare.le_trans (nat.le_inc _)
      apply smallest_factor_from.ge_start n fuel x.inc
    }
    apply Compare.le_id

#print axioms smallest_factor_from.ge_start

theorem smallest_factor_from.is_dvd (n: nat) :
  ∀fuel x h₀ h₁ h₂, smallest_factor_from fuel x n h₀ h₁ h₂ ∣ n
 := by
  intro fuel x h₀ h₁ h₂
  unfold smallest_factor_from
  match fuel with
  | .zero =>
    have := Compare.not_lt_and_le h₀
    contradiction
  | .inc fuel =>
    simp
    cases h:dvd.dec <;> simp
    {
      apply smallest_factor_from.is_dvd n fuel x.inc
    }
    assumption

#print axioms smallest_factor_from.ge_start

theorem smallest_factor.prf (n: nat) :
  ∀y, nat.zero.inc.inc <= y -> y ∣ n -> n.smallest_factor <= y
 := by
  intro y two_le_y y_dvd
  unfold nat.smallest_factor
  match n with
  | .zero => apply nat.zero_le
  | .inc .zero =>
    simp
    have ⟨ x, prf ⟩  := y_dvd
    have ⟨ y_eq_one, _ ⟩  := nat.mul_eq_one prf.symm
    rw [y_eq_one]
    apply Compare.le_id
  | .inc (.inc n) =>
    simp
    apply smallest_factor_from.prf
    assumption
    assumption

#print axioms smallest_factor.prf

theorem dvd.of_eq {a b: nat} (a_eq_b: a = b) : dvd a b := by
  rw [a_eq_b]
  exact dvd.id _

theorem smallest_factor.nz (n: nat) : n ≠ .zero -> n.smallest_factor ≠ .zero := by
  intro one_lt_n
  match n with
  | .zero => contradiction
  | .inc .zero => exact nat.noConfusion
  | .inc (.inc n) =>
  unfold nat.smallest_factor
  simp
  intro eq
  have := smallest_factor_from.ge_start n.inc.inc n.inc nat.zero.inc.inc (nat.smallest_factor.proof_1 _) (nat.smallest_factor.proof_2 _) nat.smallest_factor.proof_3
  rw [eq] at this
  contradiction

#print axioms smallest_factor.nz

theorem smallest_factor.ge_two (n: nat) : nat.zero.inc < n -> nat.zero.inc.inc <= n.smallest_factor := by
  intro one_lt_n
  match n with
  | .zero | .inc .zero => contradiction
  | .inc (.inc n) =>
  unfold nat.smallest_factor
  simp
  apply smallest_factor_from.ge_start

#print axioms smallest_factor.ge_two

theorem smallest_factor.is_dvd (n: nat) : n.smallest_factor ∣ n := by
  match n with
  | .zero | .inc .zero => apply dvd.id
  | .inc (.inc n) =>
  unfold nat.smallest_factor
  simp
  apply smallest_factor_from.is_dvd

#print axioms smallest_factor.ge_two

theorem smallest_factor.prime (n: nat) : nat.zero.inc < n -> n.smallest_factor.prime := by
  intro one_lt_n
  have prf := smallest_factor.prf n
  match n with
  | .zero | .inc .zero => contradiction
  | .inc (.inc n) =>
  apply And.intro
  unfold nat.smallest_factor
  simp
  intro h
  have := dvd.of_eq h
  have smallest_le := dvd.is_le this nat.noConfusion
  have smallest_ge := smallest_factor_from.ge_start n.inc.inc n.inc nat.zero.inc.inc (by
    repeat rw [nat.add_inc_right]
    rw [nat.add_zero_right]
    apply nat.to_lt_inc_irr
    apply nat.to_lt_inc_irr
    apply nat.lt_inc) (by
    apply nat.to_le_inc_irr
    apply nat.to_le_inc_irr
    apply nat.zero_le) nat.noConfusion
  have := Compare.le_trans smallest_ge smallest_le
  contradiction
  intro x
  have smallest_ge := smallest_factor.ge_two n.inc.inc (by 
    apply nat.to_lt_inc_irr
    apply nat.zero_lt_inc)
  match x with
  | .zero =>
    apply Or.inl
    intro zero_dvd
    have ⟨ x, prf ⟩ := zero_dvd
    rw [nat.mul_zero_left] at prf 
    rw [prf] at smallest_ge
    contradiction
  | .inc .zero =>
    apply Or.inr
    apply Or.inr
    rfl
  | .inc (.inc x) =>
  cases h:@dvd.dec x.inc.inc (nat.smallest_factor (nat.inc (nat.inc n))) nat.noConfusion
  apply Or.inl
  assumption
  apply Or.inr
  apply Or.inl
  have := prf x.inc.inc (by
    apply nat.to_le_inc_irr
    apply nat.to_le_inc_irr
    apply nat.zero_le) (by 
    apply dvd.trans _ (smallest_factor.is_dvd n.inc.inc)
    assumption)
  next dvd_smallest => {
    have := dvd_smallest.is_le (by
      intro smallest_eq
      rw [smallest_eq] at smallest_ge
      contradiction)
    apply Compare.le_to_eq
    assumption
    assumption
  }

#print axioms smallest_factor.prime

def nat.prime.ne_zero (p: nat.prime n) : n ≠ nat.zero := by
  intro n_eq_zero
  match p.right nat.zero.inc.inc with
    | .inl h =>
      rw [n_eq_zero] at h
      exact h (dvd.zero _)
    | .inr (.inl h) =>
      rw [n_eq_zero] at h
      exact nat.noConfusion h
    | .inr (.inr h) => 
      contradiction

#print axioms nat.prime.ne_zero

def nat.prime.ne_one (p: nat.prime n) : n ≠ nat.zero.inc := p.left

#print axioms nat.prime.ne_one
