import Alg.Nat.PrimeFactors
import Alg.ListProps.Sorted.Intersect

def contrapositive : (P -> Q) -> ¬ Q -> ¬ P := by
  intro p_to_q not_q p
  exact not_q (p_to_q p)

theorem list_product.of_sorted_intersect :
  ∀{as bs: List nat},
  as.sorted ->
  bs.sorted ->
  as.allP nat.prime ->
  bs.allP nat.prime ->
  list_product (as.sorted_intersect bs) = (list_product as).gcd (list_product bs) := by
  apply List.sorted.induction
  {
    intro bs
    intro _ _ _ _
    rw [List.sorted_intersect.empty_left, list_product.empty]
    rw [nat.gcd.one_left]
  }
  {
    intro a as
    intro _ _ _ _
    rw [List.sorted_intersect.empty_right, list_product.empty]
    rw [nat.gcd.one_right]
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort as_primes bs_primes
    rw [List.sorted_intersect.induct_lt a_ord_b]
    conv => {
      rhs
      lhs
      unfold list_product
    }

    rw [nat.gcd.cancel_left]
    {
      apply prev
      exact as_sort.pop
      assumption
      exact as_primes.right
      assumption
    }
    {
      have not_con := List.not_contains_sorted a_ord_b bs_sort
      generalize b_fact_def:PrimeFactorization.mk (b::bs) bs_primes rfl bs_sort = b_fact
      have b_complete := b_fact.is_complete a as_primes.left
      rw [←b_fact_def] at b_complete
      have not_dvd := contrapositive b_complete not_con
      match nat.prime.to_coprime_or_dvd as_primes.left (list_product (b::bs)) with
      | .inr _ => contradiction
      | .inl a_coprime_bs => exact a_coprime_bs
    }
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort as_primes bs_primes
    rw [List.sorted_intersect.induct_eq a_ord_b]
    simp
    have a_eq_b : a = b := Compare.ord_to_eq a_ord_b
    rw [←a_eq_b, nat.gcd.mul_left]
    apply nat.to_mul_irr_left
    apply prev
    exact as_sort.pop
    exact bs_sort.pop
    exact as_primes.right
    exact bs_primes.right
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort as_primes bs_primes
    rw [List.sorted_intersect.induct_gt a_ord_b]
    conv => {
      rhs
      rhs
      unfold list_product
    }

    rw [nat.gcd.comm, nat.gcd.cancel_left, nat.gcd.comm]
    {
      apply prev
      assumption
      exact bs_sort.pop
      assumption
      exact bs_primes.right
    }
    {
      have not_con := List.not_contains_sorted (Compare.flip a_ord_b) as_sort
      generalize a_fact_def:PrimeFactorization.mk (a::as) as_primes rfl as_sort = a_fact
      have a_complete := a_fact.is_complete b bs_primes.left
      rw [←a_fact_def] at a_complete
      have not_dvd := contrapositive a_complete not_con
      match nat.prime.to_coprime_or_dvd bs_primes.left (list_product (a::as)) with
      | .inr _ => contradiction
      | .inl a_coprime_bs => exact a_coprime_bs
    }
  }

#print axioms list_product.of_sorted_intersect

theorem PrimeFactorization.intersect
  (fa: PrimeFactorization a)
  (fb: PrimeFactorization b):
  PrimeFactorization (a.gcd b) := by
  apply PrimeFactorization.mk (fa.factors.sorted_intersect fb.factors)
  apply List.subset_of.allP
  apply List.sorted_intersect.subset_of_left
  exact fa.sorted
  exact fb.sorted
  exact fa.all_primes
  rw [list_product.of_sorted_intersect]
  rw [←fa.eq_n]
  rw [←fb.eq_n]
  exact fa.sorted
  exact fb.sorted
  exact fa.all_primes
  exact fb.all_primes
  apply List.sorted_intersect.keeps_sorted
  exact fa.sorted
  exact fb.sorted

#print axioms PrimeFactorization.intersect
