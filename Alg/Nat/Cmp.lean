import Alg.Nat
import Alg.Compare

def nat.ord (a b: nat): Order := match a with
  | .zero => match b with
    | .zero => Order.Eq
    | .inc _ => Order.Less
  | .inc a₀ => match b with
    | .zero => Order.Greater
    | .inc b₀ => a₀.ord b₀

#print axioms nat.ord

def nat.ord_flip (a b: nat): nat.ord a b = (nat.ord b a).flip := by
  cases a <;> cases b
  repeat rfl
  simp
  next a₀ b₀ => {
    unfold ord
    simp
    rw [@nat.ord_flip a₀ b₀]
    unfold Order.flip
    rfl
  }

#print axioms nat.ord_flip

def nat.ord_id (a: nat) : nat.ord a a = Order.Eq := by
  cases a
  rfl
  unfold ord
  simp
  apply nat.ord_id

#print axioms nat.ord_id

def nat.ord_to_eq {a b: nat} : nat.ord a b = Order.Eq -> a = b := by
  intro ord_ab
  cases a <;> cases b
  rfl
  contradiction
  contradiction
  apply nat.to_inc_irr
  unfold ord at ord_ab
  simp at ord_ab
  exact nat.ord_to_eq ord_ab

#print axioms nat.ord_to_eq

def nat.ord_transitive {a b c: nat} {o: Order} : nat.ord a b = o -> nat.ord b c = o -> nat.ord a c = o := by
  intro ord_ab ord_bc
  cases a <;> cases b <;> cases c
  any_goals assumption
  
  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  rw [←ord_ab] at ord_bc
  contradiction
  
  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  rw [←ord_ab] at ord_bc
  contradiction

  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  unfold ord; simp
  apply nat.ord_transitive ord_ab ord_bc

#print axioms nat.ord_transitive

instance nat.cmp : Compare nat where
  ord := nat.ord
  ord_flip := nat.ord_flip
  ord_id := nat.ord_id
  ord_to_eq := nat.ord_to_eq
  ord_transitive := nat.ord_transitive

#print axioms nat.cmp

instance nat.zero_lt_inc (x: nat) : .zero < inc x := rfl

#print axioms nat.zero_lt_inc

instance nat.zero_le (x: nat) : .zero <= x := match x with | .zero => Or.inr rfl | .inc _ => Or.inl rfl

#print axioms nat.zero_lt_inc

instance nat.gt_zero {a b: nat} : a < b -> nat.zero < b := Compare.le_lt_trans (nat.zero_le a)

#print axioms nat.zero_lt_inc

instance nat.ord_inc_irr (a b: nat) : ord (inc a) (inc b) = ord a b := by
  conv => {
    lhs
    unfold Compare.ord nat.cmp nat.ord
  }

#print axioms nat.ord_inc_irr

instance nat.to_lt_inc_irr (a b: nat) : a < b -> inc a < inc b := by
  intro a_lt_b
  unfold LT.lt ord_lt nat.cmp nat.ord
  simp
  rw [nat.ord_inc_irr a b]
  exact a_lt_b

#print axioms nat.to_lt_inc_irr

instance nat.to_le_inc_irr (a b: nat) : a <= b -> inc a <= inc b := by
  intro a_le_b
  match a_le_b with
  | .inl a_lt_b =>
    apply Or.inl
    unfold Compare.ord nat.cmp nat.ord; simp
    assumption
  | .inr a_eq_b =>
    apply Or.inr
    unfold Compare.ord nat.cmp nat.ord; simp
    assumption

#print axioms nat.to_le_inc_irr

instance nat.to_gt_inc_irr (a b: nat) : a > b -> inc a > inc b := by
  intro a_lt_b
  unfold GT.gt LT.lt ord_lt nat.cmp nat.ord
  simp
  exact a_lt_b

#print axioms nat.to_gt_inc_irr

instance nat.to_ge_inc_irr (a b: nat) : a >= b -> inc a >= inc b := by
  intro a_le_b
  match a_le_b with
  | .inl a_lt_b =>
    apply Or.inl
    unfold Compare.ord nat.cmp nat.ord; simp
    assumption
  | .inr a_eq_b =>
    apply Or.inr
    unfold Compare.ord nat.cmp nat.ord; simp
    assumption

#print axioms nat.to_ge_inc_irr

instance nat.of_lt_inc_irr {a b: nat} : inc a < inc b -> a < b := by
  intro a_lt_b
  unfold LT.lt ord_lt nat.cmp nat.ord at a_lt_b
  simp at a_lt_b
  rw [nat.ord_inc_irr a b] at a_lt_b
  exact a_lt_b

#print axioms nat.of_lt_inc_irr

instance nat.of_le_inc_irr {a b: nat} : inc a <= inc b -> a <= b := by
  intro a_le_b
  match a_le_b with
  | .inl a_lt_b =>
    apply Or.inl
    unfold Compare.ord nat.cmp nat.ord at a_lt_b
    assumption
  | .inr a_eq_b =>
    apply Or.inr
    unfold Compare.ord nat.cmp nat.ord at a_eq_b
    assumption

#print axioms nat.of_le_inc_irr

instance nat.of_gt_inc_irr {a b: nat} : inc a > inc b -> a > b := by
  intro a_lt_b
  unfold GT.gt LT.lt ord_lt nat.cmp nat.ord
  simp
  exact a_lt_b

#print axioms nat.of_gt_inc_irr

instance nat.of_ge_inc_irr {a b: nat} : inc a >= inc b -> a >= b := by
  intro a_le_b
  match a_le_b with
  | .inl a_lt_b =>
    apply Or.inl
    unfold Compare.ord nat.cmp nat.ord at a_lt_b
    assumption
  | .inr a_eq_b =>
    apply Or.inr
    unfold Compare.ord nat.cmp nat.ord at a_eq_b
    assumption

#print axioms nat.of_ge_inc_irr

instance nat.not_inc_le_zero (x : nat) : ¬nat.inc x <= nat.zero := by
  intro inc_le_zero
  cases inc_le_zero <;> contradiction

#print axioms nat.not_inc_le_zero

instance nat.le_zero : x <= nat.zero -> x = nat.zero := by
  intro x_le_zero
  match x with
  | .zero => rfl
  | .inc x =>
    have := nat.not_inc_le_zero x
    contradiction

#print axioms nat.le_zero

instance nat.not_lt_zero (x : nat) : ¬x < nat.zero := by
  intro x_lt_zero
  unfold LT.lt ord_lt Compare.ord nat.cmp nat.ord at x_lt_zero
  simp at x_lt_zero
  unfold nat.ord at x_lt_zero
  cases x <;> contradiction

#print axioms nat.not_lt_zero

instance nat.le_to_lt_inc {a b : nat} :   a <= b -> a < nat.inc b := by
  intro a_le_b
  cases a 
  exact nat.zero_lt_inc _
  apply nat.to_lt_inc_irr
  match b with
  | .inc b₀ =>
  apply nat.le_to_lt_inc
  assumption

#print axioms nat.le_to_lt_inc

instance nat.lt_inc_to_le {a b : nat} : a < nat.inc b -> a <= b := by
  intro a_le_b
  cases a
  exact nat.zero_le _
  have a_le_b := nat.of_lt_inc_irr a_le_b
  have := nat.gt_zero a_le_b
  match b with
  | .inc b₀ =>
  apply nat.to_le_inc_irr
  apply nat.lt_inc_to_le
  assumption
  
#print axioms nat.lt_inc_to_le

def nat.ne_zero_to_gt_zero {a:nat} : a ≠ .zero -> nat.zero < a := fun h => by
  match a with
  | .inc _ =>
  apply nat.zero_lt_inc

#print axioms nat.ne_zero_to_gt_zero

def nat.lt_inc (a:nat) : a < inc a := match a with
  | .zero => rfl
  | .inc a₀ => by
    apply nat.to_lt_inc_irr
    apply nat.lt_inc

#print axioms nat.lt_inc

def nat.le_inc (a:nat) : a <= inc a := Or.inl (nat.lt_inc a)

#print axioms nat.lt_inc

instance nat.WF : WellFoundedRelation nat where
  rel a b := a < b
  wf := by
    apply WellFounded.intro
    intro a
    induction a with
    | zero => 
      apply Acc.intro
      intro x
      have := nat.not_lt_zero x
      intro
      contradiction
    | inc a₀ ih =>
      apply Acc.intro
      intro x x_lt_a₀
      match nat.lt_inc_to_le x_lt_a₀ with
      | .inr e => rw [Compare.ord_to_eq e]; assumption
      | .inl e => exact ih.inv e

#print axioms nat.WF
  