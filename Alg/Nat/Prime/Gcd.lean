import Alg.Nat.Prime
import Alg.Nat.Gcd

def nat.prime.to_coprime_or_dvd (p: nat.prime n): ∀x, nat.coprime n x ∨ n ∣ x := by
  intro x
  have ⟨ gcd_dvd_n, gcd_dvd_x ⟩  := gcd.is_dvd n x
  match p.right (gcd n x) with
  | .inl h => contradiction
  | .inr (.inl h) =>
    rw [h] at gcd_dvd_x
    apply Or.inr
    assumption
  | .inr (.inr h) =>
    apply Or.inl
    assumption

#print axioms nat.prime.to_coprime_or_dvd

def nat.prime.ne_implies_coprime (pn: nat.prime n) (pm: nat.prime m) (n_ne_m: n ≠ m): nat.coprime n m := by
  match pn.to_coprime_or_dvd m with
  | .inl coprime => exact coprime
  | .inr n_dvd_m => match pm.right n with
    | .inl _ | .inr (.inl _) => contradiction
    | .inr (.inr h) =>
      rw [h] at pn
      exact (pn.left rfl).elim

#print axioms nat.prime.ne_implies_coprime
