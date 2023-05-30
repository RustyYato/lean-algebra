import Alg.Nat.PrimeFactors
import Alg.ListProps.Sorted.Merge

theorem list_product.of_sorted_merge :
  ∀{as bs: List nat},
  list_product (as.sorted_merge bs) = (list_product as) * (list_product bs) := by
  apply List.sorted.induction
  {
    intro bs
    rw [List.sorted_merge.empty_left, list_product.empty, nat.mul_one_left]
  }
  {
    intro a as
    rw [List.sorted_merge.empty_right, list_product.empty, nat.mul_one_right]
  }
  {
    intro a as b bs a_ord_b prev
    rw [List.sorted_merge.induct_lt a_ord_b]
    conv => {
      lhs
      unfold list_product
    }
    conv => {
      rhs
      lhs
      unfold list_product
    }
    rw [nat.mul_perm_ab_c_to_a_bc]
    apply nat.to_mul_irr_left
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [List.sorted_merge.induct_eq a_ord_b]
    simp
    rw [nat.mul_perm_ab_c_to_a_bc]
    apply nat.to_mul_irr_left
    rw [nat.mul_perm_a_bc_to_b_ac]
    apply nat.to_mul_irr_left
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [List.sorted_merge.induct_gt a_ord_b]
    conv => {
      lhs
      unfold list_product
    }
    conv => {
      rhs
      rhs
      unfold list_product
    }
    rw [nat.mul_perm_a_bc_to_b_ac]
    apply nat.to_mul_irr_left
    assumption
  }

#print axioms list_product.of_sorted_merge

def PrimeFactorization.merge
  (fa: PrimeFactorization a)
  (fb: PrimeFactorization b):
  PrimeFactorization (a * b) := by
  apply PrimeFactorization.mk (fa.factors.sorted_merge fb.factors)
  apply List.sorted_merge.keeps_allP
  exact fa.all_primes
  exact fb.all_primes
  rw [list_product.of_sorted_merge]
  rw [←fa.eq_n]
  rw [←fb.eq_n]
  apply List.sorted_merge.keeps_sorted
  exact fa.sorted
  exact fb.sorted

#print axioms PrimeFactorization.merge

theorem PrimeFactorization.merge.proof
  (fa: PrimeFactorization a)
  (fb: PrimeFactorization b)
  (fab: PrimeFactorization (a * b)):
  fab.factors = fa.factors.sorted_merge fb.factors := by
  generalize h:PrimeFactorization.merge fa fb = fab'
  unfold merge at h
  rw [Subsingleton.allEq fab fab']
  rw [←h]

#print axioms PrimeFactorization.merge.proof
