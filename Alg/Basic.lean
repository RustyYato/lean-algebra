theorem contrapositive {P Q : Prop} : (P → Q) -> (¬ Q → ¬ P) := by
  intro h
  intro nq p
  exact nq (h p)

def left_concat_eq_append : a::as = [a] ++ as := rfl

#print axioms left_concat_eq_append

theorem _append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    repeat rw [List.cons_append]
    congr

#print axioms _append_assoc

theorem _fold_append (as bs : List α) : as.append bs = as ++ bs := rfl

#print axioms _append_assoc

theorem _append_cons (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.cons_append]
    rw [ih]
    rw [List.cons_append]
    rw [List.cons_append]

#print axioms _append_cons
