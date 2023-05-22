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
