import Alg.Nat.PrimeFactors
import Alg.ListProps.Sorted.Induction
import Alg.Basic

theorem PrimeFactorization.of_sub_list_raw
  (a_factors: List nat)
  (b_factors: List nat):
  a_factors.sublist_of b_factors ->
  list_product a_factors ∣ list_product b_factors := by
  intro sub
  match a_factors with
  | [] => exact dvd.one _
  | a::as =>
  match b_factors with
  | b::bs =>
    unfold List.sublist_of at sub
    simp at sub
    match sub with
    | .inl ⟨ a_eq_b, sub ⟩ =>
      rw [a_eq_b]
      simp
      apply dvd.to_mul_com_left
      apply of_sub_list_raw
      assumption
    | .inr sub =>
      conv => {
        rhs
        simp
      }
      have := dvd.mul_right b (list_product bs)
      apply dvd.trans _ this
      apply of_sub_list_raw
      assumption

#print axioms PrimeFactorization.of_sub_list_raw

theorem PrimeFactorization.to_sub_list_raw:
  ∀(a_factors: List nat) (b_factors: List nat),
  a_factors.sorted ->
  b_factors.sorted ->
  a_factors.allP nat.prime ->
  b_factors.allP nat.prime ->
  list_product a_factors ∣ list_product b_factors ->
  a_factors.sublist_of b_factors 
   := by
  apply List.sorted.induction
  {
    intro bs
    intro _ _ _ _ _
    exact List.sublist_of.empty
  }
  {
    intro a as
    intro _ _ a_primes _ dvd_a_b
    have ⟨ _, prf ⟩  := dvd_a_b
    have ⟨ prf, _ ⟩   := nat.mul_eq_one prf.symm
    have all_eq_one := list_product.eq_one prf.symm
    have all_ne_one := a_primes.map (fun x => x.ne_one)
    have := all_eq_one.and_all_not all_ne_one
    contradiction
  }
  {
    intro a as b bs a_ord_b _
    intro _ b_sort a_primes b_primes dvd_a_b
    apply False.elim

    -- we have a prime number (a) that isn't in the list b::bs
    -- which means that dvd_a_b is False

    have b_complete := PrimeFactorization.is_complete_raw (b::bs) b_primes rfl

    have := b_sort.contains (b_complete a a_primes.left (
      dvd.trans (by
        simp
        apply dvd.mul_left
      ) dvd_a_b
    ))
    
    have := Compare.not_lt_and_le a_ord_b

    contradiction
  }
  {
    intro a as b bs a_ord_b prev
    intro a_sort b_sort a_primes b_primes dvd_a_b

    rw [Compare.ord_to_eq a_ord_b]
    rw [Compare.ord_to_eq a_ord_b] at dvd_a_b
    apply List.sublist_of.push
    apply prev
    exact a_sort.pop
    exact b_sort.pop
    exact a_primes.right
    exact b_primes.right
    exact dvd.mul_cancel_com_left b_primes.left.ne_zero dvd_a_b
  }
  {
    intro a as b bs a_ord_b prev
    intro a_sort b_sort a_primes b_primes dvd_a_b
    apply List.sublist_of.push_right
    apply prev

    assumption
    exact b_sort.pop
    assumption
    exact b_primes.right
    apply nat.coprime.cancel_left _ dvd_a_b


    have a_complete := PrimeFactorization.is_complete_raw (a::as) a_primes rfl


    have as_not_contains_b := contrapositive a_sort.contains (Compare.not_lt_and_le (Compare.flip a_ord_b))
    have not_divis_b_as := contrapositive (a_complete b b_primes.left) as_not_contains_b 

    match b_primes.left.to_coprime_or_dvd (list_product $ a::as) with
    | .inr _ => contradiction
    | .inl _ => assumption
  }
  
#print axioms PrimeFactorization.of_sub_list_raw

theorem PrimeFactorization.of_sub_list
  (pa: PrimeFactorization an)
  (pb: PrimeFactorization bn):
  pa.factors.sublist_of pb.factors ->
  an ∣ bn := by
  intro sub
  rw [pa.eq_n, pb.eq_n]
  exact PrimeFactorization.of_sub_list_raw pa.factors pb.factors sub

#print axioms PrimeFactorization.of_sub_list

theorem PrimeFactorization.to_sub_list
  (pa: PrimeFactorization an)
  (pb: PrimeFactorization bn):
  an ∣ bn ->
  pa.factors.sublist_of pb.factors := by
  intro dvd_a_b
  rw [pa.eq_n, pb.eq_n] at dvd_a_b
  apply PrimeFactorization.to_sub_list_raw pa.factors pb.factors
  exact pa.sorted
  exact pb.sorted
  exact pa.all_primes
  exact pb.all_primes
  assumption

#print axioms PrimeFactorization.to_sub_list
