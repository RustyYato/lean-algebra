import Alg.Nat.Prime
import Alg.Nat.Divisible.Division
import Alg.ListProps.Sorted

@[simp]
def list_product (list: List nat) := match list with
   | [] => nat.zero.inc
   | x ::xs => x * list_product xs

#print axioms list_product

structure PrimeFactorization (n: nat) where
  factors: List nat
  all_primes: factors.allP nat.prime
  eq_n: n = list_product factors
  sorted: factors.sorted

#print axioms PrimeFactorization

def List.sorted_push.list_product_def (list: List nat) (x: nat) : list_product (list.sorted_push x) = (list_product list) * x := by
  unfold sorted_push
  match list with
  | [] =>
    simp
    exact nat.mul_comm _ _
  | a::as =>  
    simp
    cases Compare.dec_le a x <;> simp
    rw [nat.mul_perm_a_bc_to_bc_a]
    rw [nat.mul_perm_ab_c_to_a_bc, nat.mul_comm a, nat.mul_comm a]
    apply nat.to_mul_irr
    apply List.sorted_push.list_product_def

#print axioms List.sorted_push.list_product_def

def PrimeFactorization.push (f: PrimeFactorization a) (b: nat) (bprime: b.prime) : PrimeFactorization (a * b) := by
  apply PrimeFactorization.mk (f.factors.sorted_push b)
  apply List.sorted_push.keeps_allP
  exact f.all_primes
  exact bprime
  rw [List.sorted_push.list_product_def, ←f.eq_n]
  apply List.sorted_push.keeps_sorted
  exact f.sorted

#print axioms PrimeFactorization.push

def nat.factorize.bounded (fuel n: nat) (n_nz: n ≠ .zero) (fuel_def: n <= fuel): PrimeFactorization n := by
  match fuel with
  | .zero => 
    have := nat.le_zero fuel_def
    contradiction
  | .inc fuel =>
    match n with
    | .zero => contradiction
    | .inc .zero =>
      apply PrimeFactorization.mk []
      trivial
      rfl
      trivial
    | .inc (.inc n) =>
    have dvd_f := smallest_factor.is_dvd n.inc.inc
    have smallest_nz := smallest_factor.nz n.inc.inc n_nz 
    have ndef := dvd_f.to_div_exact smallest_nz
    have small_ge_two := smallest_factor.ge_two n.inc.inc (by
      apply nat.to_lt_inc_irr
      apply nat.zero_lt_inc)
    have dv_lt_n := nat.mul_factor_lt ndef nat.noConfusion small_ge_two
    have := nat.factorize.bounded fuel (n.inc.inc / (n.inc.inc.smallest_factor)) (by
      intro dv_eq_zero
      rw [dv_eq_zero] at ndef
      rw [nat.mul_zero_left] at ndef
      contradiction) (by
        apply Compare.le_trans _ (nat.of_le_inc_irr fuel_def)
        exact nat.lt_inc_to_le dv_lt_n)
    have := this.push n.inc.inc.smallest_factor (smallest_factor.prime _ (by apply nat.to_lt_inc_irr; apply nat.zero_lt_inc))
    rw [←ndef] at this
    exact this

#print axioms nat.factorize.bounded

def nat.factorize (n: nat) (n_nz: n ≠ .zero): PrimeFactorization n :=
  nat.factorize.bounded n n n_nz (Compare.le_id _)

#print axioms nat.factorize
