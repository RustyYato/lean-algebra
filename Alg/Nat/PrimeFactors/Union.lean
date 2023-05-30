import Alg.Nat.PrimeFactors.Difference
import Alg.Nat.PrimeFactors.Sublist
import Alg.Nat.PrimeFactors.Intersect
import Alg.Nat.PrimeFactors.Merge
import Alg.ListProps.Sorted.SetOps
import Alg.Nat.Lcm

def PrimeFactorization.union
  (pa: PrimeFactorization a)
  (pb: PrimeFactorization b):
  PrimeFactorization (nat.lcm a b) := by
  unfold nat.lcm
  apply (pa.merge pb).difference (pa.intersect pb)
  apply dvd.trans (nat.gcd.is_dvd a b).left
  apply dvd.mul_left

theorem PrimeFactorization.union.proof
  (fa: PrimeFactorization a)
  (fb: PrimeFactorization b)
  (fab: PrimeFactorization (a.lcm b)):
  fab.factors = fa.factors.sorted_union fb.factors := by
  generalize h:PrimeFactorization.union fa fb = fab'
  rw [Subsingleton.allEq fab fab']
  rw [←h]
  unfold union
  rw [List.sorted.union_def]
  rfl
  exact fa.sorted
  exact fb.sorted

#print axioms PrimeFactorization.union.proof
