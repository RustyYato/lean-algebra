import Alg.Nat.PrimeFactors.Sublist
import Alg.ListProps.Sorted.Difference
import Alg.Nat.Divisible.Division


theorem PrimeFactorization.difference_raw:
  ∀(a_factors: List nat)
  (b_factors: List nat),
  (list_product b_factors) ∣ (list_product a_factors) ->
  b_factors.sublist_of a_factors ->
  a_factors.allP nat.prime ->
  b_factors.allP nat.prime ->
  a_factors.sorted ->
  b_factors.sorted ->
  (list_product a_factors) / (list_product b_factors) =
  list_product (a_factors.sorted_difference b_factors) := by
  apply List.sorted.induction
  {
    intro bs
    intro dvd_b_a sub _ b_primes _ b_sort
    match bs with
    | [] =>
    rfl
  }
  {
    intro a as
    intro _ _ _ _ _ _
    simp
    rw [nat.div_one]
  }
  {
    intro a as b bs a_ord_b prev
    intro dvd_b_a sub a_primes b_primes a_sort b_sort
    rw [List.sorted_difference.induct_lt a_ord_b]
    simp
    have not_con : ¬List.containsP (b :: bs) a  := b_sort.not_contains a_ord_b
    have co_prime : nat.coprime a (list_product (b :: bs)) := by
      have := PrimeFactorization.is_complete_raw (b::bs) b_primes rfl
      have := contrapositive (this a a_primes.left) not_con
      match a_primes.left.to_coprime_or_dvd (list_product (b::bs)) with
      | .inr _ => contradiction
      | .inl _ => assumption
    rw [nat.div_mul_assoc]
    {
      apply nat.to_mul_irr_left
      apply prev
      apply co_prime.cancel_left dvd_b_a
      apply sub.pop_right
      assumption
      exact a_primes.right
      assumption
      exact a_sort.pop
      assumption
    }
    apply co_prime.cancel_left dvd_b_a
  }
  {
    intro a as b bs a_ord_b prev
    intro dvd_b_a sub a_primes b_primes a_sort b_sort
    rw [List.sorted_difference.induct_eq a_ord_b]
    simp
    rw [Compare.ord_to_eq a_ord_b] at *
    have : list_product bs ∣ list_product as := by
      have ⟨ x, prf ⟩ := dvd_b_a
      simp at prf
      rw [nat.mul_comm b, nat.mul_comm b] at prf
      exists x
      apply nat.of_mul_irr
      rw [prf]
      rw [nat.mul_perm_ab_c_to_ac_b]
      exact b_primes.left.ne_zero
    rw [nat.div_eq_div]
    {
      rw [nat.div_id, nat.mul_one_left]
      apply prev
      assumption
      apply List.sublist_of.pop sub
      exact a_primes.right
      exact b_primes.right
      exact a_sort.pop
      exact b_sort.pop
      exact b_primes.left.ne_zero
    }
    apply dvd.id
    assumption
  }
  {
    intro a as b bs a_ord_b _
    intro dvd_b_a _ a_primes b_primes a_sort _
    rw [List.sorted_difference.induct_gt a_ord_b]
    
    have not_con : ¬ (a::as).containsP b := by
      exact a_sort.not_contains (Compare.flip a_ord_b)
    have : ¬ b ∣ list_product (a::as) := by
      have := PrimeFactorization.is_complete_raw (a::as) a_primes rfl
      exact contrapositive (this b b_primes.left) not_con
    
    have : b ∣ list_product (a::as) := by
      apply dvd.trans _ dvd_b_a
      simp
      apply dvd.mul_left
    
    contradiction
  }

#print axioms PrimeFactorization.difference_raw

def PrimeFactorization.difference
  (pa: PrimeFactorization an)
  (pb: PrimeFactorization bn):
  bn ∣ an ->
  PrimeFactorization (an / bn) := by
  intro sub
  rw [pa.eq_n, pb.eq_n]
  apply PrimeFactorization.mk (pa.factors.sorted_difference pb.factors)
  have := (pa.factors.sorted_difference pb.factors)
  apply List.sorted_difference.sublist_of_left.allP
  exact pa.all_primes
  {
    apply PrimeFactorization.difference_raw
    rw [←pa.eq_n, ←pb.eq_n]
    assumption
    exact PrimeFactorization.to_sub_list pb pa sub
    exact pa.all_primes
    exact pb.all_primes
    exact pa.sorted
    exact pb.sorted
  }
  apply List.sorted_difference.keeps_sorted
  exact pa.sorted
  exact pb.sorted

#print axioms PrimeFactorization.difference
