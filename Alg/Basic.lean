theorem contrapositive {P Q : Prop} : (P → Q) -> (¬ Q → ¬ P) := by
  intro h
  intro nq p
  exact nq (h p)
