import Alg.Nat.Prime.Gcd
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

def PrimeFactorization.is_complete_raw 
  (factors: List nat)
  (all_primes: factors.allP nat.prime)
  (eq_n: n = list_product factors): ∀p:nat, p.prime -> p ∣ n -> factors.containsP p := by
  intro p pprime p_dvd_n
  match factors with
  | [] => 
    simp at eq_n
    rw [eq_n] at p_dvd_n
    have ⟨ _, prf ⟩ := p_dvd_n
    have ⟨ p_eq_one, _ ⟩  := nat.mul_eq_one prf.symm
    rw [p_eq_one] at pprime
    have ⟨ ne_one, _ ⟩  := pprime
    contradiction
  | a::as =>
    simp at eq_n
    match decEq p a with
    | .isTrue h =>  
      rw [h]
      unfold List.containsP  List.anyP
      apply Or.inl
      rfl
    | .isFalse p_ne_a =>
      apply List.containsP.pop
      apply PrimeFactorization.is_complete_raw as _ rfl
      any_goals assumption
      rw [eq_n] at p_dvd_n
      have coprime_p_a := nat.prime.ne_implies_coprime pprime all_primes.left p_ne_a
      exact coprime_p_a.comm.cancel_left p_dvd_n
      exact all_primes.right

#print axioms PrimeFactorization.is_complete_raw

def PrimeFactorization.is_complete (f: PrimeFactorization n) : ∀p:nat, p.prime -> p ∣ n -> f.factors.containsP p := 
  PrimeFactorization.is_complete_raw f.factors f.all_primes f.eq_n

#print axioms PrimeFactorization.is_complete

def sorted_min [Compare α] {x:α} {xs: List α} (xsorted: (x::xs).sorted) : ∀y, (x::xs).containsP y -> x <= y := by
  intro y xs_contains
  match xs_contains with
  | .inl y_eq_x => apply Or.inr (Compare.ord_from_eq y_eq_x.symm)
  | .inr xs_contains =>
  match xs with
  | [] => contradiction
  | x'::xs' =>
    have y_le_x' := sorted_min (List.sorted.pop _ _ xsorted) y xs_contains
    apply Compare.le_trans _ y_le_x'
    exact xsorted.left

def nat.smallest_prime_factor (f: PrimeFactorization n) : f.factors = x :: xs ->
  x.prime ∧ ∀y, y.prime -> y ∣ n -> x <= y
  := by
    match f with
    | .mk nfactors nprimes ndef nsorted =>
    intro factors
    simp at factors
    rw [factors] at nprimes nsorted ndef
    clear factors nfactors f
    apply And.intro
    exact nprimes.left
    intro y yprime ydvd
    have is_complete := PrimeFactorization.is_complete_raw (x::xs) nprimes ndef
    exact sorted_min nsorted y (is_complete y yprime ydvd)

#print axioms nat.smallest_prime_factor

theorem zero_not_prime: ¬ nat.prime nat.zero := fun p => match p.right nat.zero.inc.inc with
   | .inl h => h (dvd.zero _)
   | .inr (.inl h) => nat.noConfusion h
   | .inr (.inr h) => nat.noConfusion (nat.of_inc_irr h)

#print axioms zero_not_prime

theorem one_not_prime: ¬ nat.prime nat.zero.inc := fun p => p.left rfl

#print axioms one_not_prime

theorem PrimeFactorization.unique_raw
  (a_factors: List nat)
  (a_all_primes: a_factors.allP nat.prime)
  (a_eq_n: n = list_product a_factors)
  (a_sorted: a_factors.sorted)
  (b_factors: List nat)
  (b_all_primes: b_factors.allP nat.prime)
  (b_eq_n: n = list_product b_factors)
  (b_sorted: b_factors.sorted):
  a_factors = b_factors := by
  match a_factors, b_factors with
  | [], [] => rfl
  | a::as, [] => 
    rw [b_eq_n] at a_eq_n
    simp at a_eq_n
    have ⟨ a_eq_one, _ ⟩  := nat.mul_eq_one a_eq_n.symm
    have a_prime := a_all_primes.left
    rw [a_eq_one] at a_prime
    have := one_not_prime
    contradiction
  | [], b::bs =>
    rw [b_eq_n] at a_eq_n
    simp at a_eq_n
    have ⟨ a_eq_one, _ ⟩  := nat.mul_eq_one a_eq_n
    have b_prime := b_all_primes.left
    rw [a_eq_one] at b_prime
    have := one_not_prime
    contradiction
  | a::as, b::bs =>
    simp at a_eq_n b_eq_n
    have a_eq_b : a = b := by
      have a_smallest := nat.smallest_prime_factor (.mk (a::as) a_all_primes a_eq_n a_sorted) rfl
      have b_smallest := nat.smallest_prime_factor (.mk (b::bs) b_all_primes b_eq_n b_sorted) rfl
      have a_dvd_n := dvd.mul_left a (list_product as)
      have b_dvd_n := dvd.mul_left b (list_product bs)
      rw [←a_eq_n] at a_dvd_n
      rw [←b_eq_n] at b_dvd_n
      have a_le_b := a_smallest.right b b_all_primes.left b_dvd_n
      have b_le_a := b_smallest.right a a_all_primes.left a_dvd_n
      apply Compare.le_to_eq
      repeat assumption
    congr
    apply PrimeFactorization.unique_raw
    exact a_all_primes.right
    rfl
    apply List.sorted.pop
    exact a_sorted
    exact b_all_primes.right
    {
      apply nat.of_mul_irr
      rw [nat.mul_comm a] at a_eq_n
      rw [nat.mul_comm b] at b_eq_n
      rw [←a_eq_n, a_eq_b, ←b_eq_n]
      intro a_eq_zero
      have := zero_not_prime
      have a_prime := a_all_primes.left
      rw [a_eq_zero] at a_prime
      contradiction
    }
    apply List.sorted.pop
    exact b_sorted

#print axioms PrimeFactorization.unique_raw

theorem PrimeFactorization.unique (a b: PrimeFactorization n): a = b := by
  have a_factors_eq_b_factors := PrimeFactorization.unique_raw
    a.factors a.all_primes a.eq_n a.sorted
    b.factors b.all_primes b.eq_n b.sorted
  match a, b with
  | .mk afact _ _ _, .mk bfact _ _ _ =>
  congr

#print axioms PrimeFactorization.unique
