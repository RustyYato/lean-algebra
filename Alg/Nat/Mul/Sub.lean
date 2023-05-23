import Alg.Nat.Sub
import Alg.Nat.Mul.Cmp

def nat.mul_sub_left (a b c: nat) :
  c <= b ->
  a * (b - c) = a * b - a * c := by 
  intro c_le_b
  match a with
  | .zero => rfl
  | .inc a₀ =>  
    rw [nat.mul_inc_left]
    rw [nat.mul_sub_left a₀ b c]
    rw [nat.add_subs]
    rw [←nat.mul_inc_left]
    rw [←nat.mul_inc_left]
    assumption
    apply nat.to_le_mul
    apply Compare.le_id
    assumption
    assumption


#print axioms nat.mul_sub_left

