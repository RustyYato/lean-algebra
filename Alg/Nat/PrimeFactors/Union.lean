import Alg.Nat.PrimeFactors.Difference
import Alg.Nat.PrimeFactors.Sublist
import Alg.Nat.PrimeFactors.Intersect
import Alg.Nat.PrimeFactors.Merge
import Alg.Nat.Lcm

def PrimeFactors.union
  (pa: PrimeFactorization a)
  (pb: PrimeFactorization b):
  PrimeFactorization (nat.lcm a b) := by
  unfold nat.lcm
  have pa_mul_b := pa.merge pb
  have pa_gcd_b := pa.intersect pb
  apply pa_mul_b.difference pa_gcd_b
  apply dvd.trans (nat.gcd.is_dvd a b).left
  apply dvd.mul_left