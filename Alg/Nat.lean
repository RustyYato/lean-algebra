inductive nat where
  | zero : nat
  | inc : nat -> nat

def nat.eq_inc_helper : nat → nat -> Prop := fun a b => match a, b with
| nat.inc a, nat.inc b => a = b
| _, _     => False

def nat.inc_irr : nat.inc a = nat.inc b -> a = b := fun h =>
  have h₁ : nat.eq_inc_helper (nat.inc a) (nat.inc a) := rfl
  have h₂ : nat.eq_inc_helper (nat.inc a) (nat.inc b) := h ▸ h₁
  h₂

#print axioms nat.inc_irr
