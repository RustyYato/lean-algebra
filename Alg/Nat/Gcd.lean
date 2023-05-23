import Alg.Nat.Divisible.Division

def gcd.induction.bounded
 {P: nat -> nat -> Sort _}
 (base: (∀b, P nat.zero b))
 (induct: (∀a b, a ≠ .zero -> P (b % a) a -> P a b))
 (x a b: nat) : a < x -> P a b :=
  fun a_lt_x =>
  match x with
  | .zero => ((nat.not_lt_zero _) a_lt_x).elim
  | .inc x =>
  match a with
  | .zero => base b
  | .inc a =>
    let prev := gcd.induction.bounded base induct x (b % a.inc) (a.inc) (by
      have := nat.rem_lt b a.inc nat.noConfusion
      apply Compare.lt_le_trans this
      exact nat.lt_inc_to_le a_lt_x)
    induct (.inc a) b nat.noConfusion prev

#print axioms gcd.induction.bounded

def gcd.induction
 {P: nat -> nat -> Sort _}
 (base: (∀b, P nat.zero b))
 (induct: (∀a b, a ≠ .zero -> P (b % a) a -> P a b))
 (a b: nat) : P a b :=
  gcd.induction.bounded base induct a.inc a b (nat.lt_inc _)

#print axioms gcd.induction

def gcd (a b: nat): nat := @gcd.induction (fun _ _ => nat) id (fun _ _ _ prev => prev) a b

def coprime (a b: nat) := gcd a b = nat.zero.inc

#print axioms gcd

example : gcd nat.zero.inc.inc.inc.inc nat.zero.inc.inc.inc.inc.inc.inc = nat.zero.inc.inc := by decide

theorem gcd.induct.step (a b x: nat) (a_lt_x: a < x.inc) (a_nz: a ≠ .zero) : b % a < x := by
  apply Compare.lt_le_trans _ (nat.lt_inc_to_le a_lt_x)
  apply nat.rem_lt
  assumption

#print axioms gcd.induct.step

theorem gcd.induction.bounded.counter_irr
  {P: nat -> nat -> Sort _}
  (base: (∀b, P nat.zero b))
  (induct: (∀a b, a ≠ .zero -> P (b % a) a -> P a b))
  : ∀(a b x y: nat), (a_lt_x: a < x) -> (a_lt_y: a < y) -> gcd.induction.bounded base induct x a b a_lt_x = gcd.induction.bounded base induct y a b a_lt_y := by
  apply gcd.induction
  {
    intro b
    intro x y a_lt_x a_lt_y
    unfold gcd.induction.bounded
    match x, y with
    | .inc _, .inc _ => rfl
  }
  {
    intro a b a_nz prev
    intro x y a_lt_x a_lt_y
    unfold gcd.induction.bounded
    have := nat.gt_zero a_lt_x
    have := nat.gt_zero a_lt_y
    match x, y with
    | .inc x, .inc y =>
    simp
    cases a with
    | zero => rfl
    | inc a =>
      simp
      rw [prev x y (gcd.induct.step a.inc b x a_lt_x nat.noConfusion) (gcd.induct.step a.inc b y a_lt_y nat.noConfusion)]
  }

#print axioms gcd.induction.bounded.counter_irr

theorem gcd.zero_left: gcd nat.zero a = a := by 
  unfold gcd
  rfl

#print axioms gcd.zero_left

theorem gcd.of_bounded (a b: nat) :
  ∀x h,
  @gcd.induction.bounded (fun _ _ => nat) id (fun _ _ _ prev => prev) x a b h = gcd a b := by
  intro a h
  unfold gcd gcd.induction
  rw [gcd.induction.bounded.counter_irr]

#print axioms gcd.of_bounded

theorem gcd.base b : gcd nat.zero b = b := rfl

#print axioms gcd.base

theorem gcd.induct {a b: nat} (a_nz: a ≠ .zero) : gcd a b = gcd (b % a) a := by
  conv => {
    lhs
    unfold gcd gcd.induction gcd.induction.bounded
  }
  match a with
  | .inc a =>
  simp
  rw [gcd.of_bounded]

#print axioms gcd.induct

theorem gcd.le : ∀(a b: nat), gcd a b <= a ∧ gcd a b <= b ∨ a = nat.zero ∨ b = nat.zero := by
  apply gcd.induction
  {
    intro b
    rw [gcd.base]
    apply Or.inr
    apply Or.inl
    rfl
  }
  {
    intro a b a_nz prev
    rw [gcd.induct a_nz]
    match b with
    | .zero =>
      apply Or.inr
      apply Or.inr
      rfl
    | .inc b =>
    apply Or.inl
    match prev with
    | .inr (.inr _) => contradiction
    | .inr (.inl rem_eq_zero) =>
      rw [rem_eq_zero, gcd.zero_left]
      apply And.intro
      apply Compare.le_id
      have := dvd.of_rem_zero a_nz rem_eq_zero
      exact this.is_le nat.noConfusion
    | .inl ⟨ left, right ⟩ =>
      clear prev
      apply And.intro
      apply Compare.le_trans right
      apply Compare.le_id
      apply Compare.le_trans left
      apply nat.rem_le 
      exact a_nz
  }

#print axioms gcd.le

theorem gcd.of_dvd : ∀ {a b x: nat}, x ∣ a -> x ∣ b -> x ∣ gcd a b := by
  apply gcd.induction
  {
    intro b
    intro x _ dvd_b
    rw [gcd.zero_left]
    exact dvd_b
  }
  {
    intro a b a_nz prev
    intro x dvd_a dvd_b
    rw [gcd.induct a_nz]
    exact (prev · dvd_a) (dvd.of_rem b a a_nz dvd_b dvd_a)
  }

#print axioms gcd.of_dvd

theorem gcd.to_dvd : ∀ {a b x: nat}, x ∣ gcd a b -> x ∣ a ∧ x ∣ b := by
  apply gcd.induction
  {
    intro b
    intro x dvd_gcd
    rw [gcd.base] at dvd_gcd
    apply And.intro
    exact dvd.zero _
    assumption
  }
  {
    intro a b a_nz prev
    intro x dvd_gcd
    rw [gcd.induct a_nz] at dvd_gcd
    have ⟨ dvd_rem, dvd_a ⟩  := prev dvd_gcd
    apply And.intro
    assumption
    exact dvd.rem_cancel_right b a a_nz dvd_a dvd_rem
  }

#print axioms gcd.to_dvd

theorem gcd.is_dvd (a b: nat) : gcd a b ∣ a ∧ gcd a b ∣ b := gcd.to_dvd (dvd.id _)

#print axioms gcd.to_dvd

theorem gcd.id (a: nat) : gcd a a = a := by
  apply dvd.to_eq
  exact (gcd.is_dvd a a).left
  exact gcd.of_dvd (dvd.id a) (dvd.id _)

#print axioms gcd.id

theorem gcd.zero_right (a: nat) : gcd a nat.zero = a := by
  apply dvd.to_eq
  exact (gcd.is_dvd a nat.zero).left
  exact gcd.of_dvd (dvd.id a) (dvd.zero _)

#print axioms gcd.zero_right

theorem gcd.comm (a b: nat) : gcd a b = gcd b a := by
  apply dvd.to_eq
  have := gcd.is_dvd a b
  apply gcd.of_dvd
  exact this.right
  exact this.left
  have := gcd.is_dvd b a
  apply gcd.of_dvd
  exact this.right
  exact this.left

#print axioms gcd.comm

theorem dvd.to_gcd_left {a b: nat} (d: a ∣ c) : gcd a b ∣ c := by
  apply dvd.trans _ d
  have := gcd.is_dvd a b
  exact (gcd.is_dvd a b).left

#print axioms dvd.to_gcd_left

theorem dvd.to_gcd_right {a b: nat} (d: b ∣ c) : gcd a b ∣ c := by
  apply dvd.trans _ d
  have := gcd.is_dvd a b
  exact (gcd.is_dvd a b).right

#print axioms dvd.to_gcd_right

theorem gcd.assoc (a b c: nat) : gcd a (gcd b c) = gcd (gcd a b) c := by
  apply dvd.to_eq
  have abc := gcd.is_dvd a (gcd b c)
  have bc := gcd.is_dvd b c
  apply gcd.of_dvd
  apply gcd.of_dvd
  exact abc.left
  apply dvd.to_gcd_right
  exact bc.left
  apply dvd.to_gcd_right
  exact bc.right
  
  have abc := gcd.is_dvd (gcd a b) c
  have ab := gcd.is_dvd a b
  apply gcd.of_dvd
  apply dvd.to_gcd_left
  exact ab.left
  apply gcd.of_dvd
  apply dvd.to_gcd_left
  exact ab.right
  exact abc.right

#print axioms gcd.assoc

theorem dvd.gcd_left {a b: nat} (d: a ∣ b) : gcd a b = a := by
  apply dvd.to_eq
  exact (gcd.is_dvd a b).left
  have := gcd.of_dvd (dvd.id _) d
  exact this

#print axioms dvd.gcd_left

theorem dvd.gcd_right {a b: nat} (d: b ∣ a) : gcd a b = b := by
  apply dvd.to_eq
  exact (gcd.is_dvd a b).right
  have := gcd.of_dvd d (dvd.id _)
  exact this

#print axioms dvd.gcd_right

theorem gcd.of_mul_dvd : ∀ {a b x: nat}, x ∣ (f * a) -> x ∣ (f * b) -> x ∣ (f * gcd a b) := by
  apply gcd.induction
  {
    intro b
    intro x _ dvd_b
    rw [gcd.zero_left]
    exact dvd_b
  }
  {
    intro a b a_nz prev
    intro x dvd_a dvd_b
    match f with
    | .zero =>
      rw [nat.mul_zero_left] at dvd_a
      rw [nat.mul_zero_left]
      assumption
    | .inc f =>
    rw [gcd.induct a_nz]
    apply prev _ dvd_a
    rw [nat.of_mul_rem]
    apply dvd.of_rem
    match a with
      | .inc a =>
        rw [nat.mul_inc_left, nat.add_inc_left]
        exact nat.noConfusion
    repeat assumption
  }

#print axioms gcd.of_mul_dvd

theorem gcd.mul_left : gcd (x * a) (x * b) = x * gcd a b := by
  apply dvd.to_eq
  {
    apply gcd.of_mul_dvd
    exact (gcd.is_dvd _ _).left
    exact (gcd.is_dvd _ _).right
  }
  {
    apply gcd.of_dvd
    apply dvd.to_mul_com_left
    exact (gcd.is_dvd a b).left
    apply dvd.to_mul_com_left
    exact (gcd.is_dvd a b).right
  }