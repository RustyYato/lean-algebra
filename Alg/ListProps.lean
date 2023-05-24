import Alg.Compare

def List.allP (list: List α) (P: α -> Prop) := match list with
  | [] => True
  | x :: xs => P x ∧ xs.allP P

def List.anyP (list: List α) (P: α -> Prop) := match list with
  | [] => False
  | x :: xs => P x ∨ xs.anyP P

def List.containsP (list: List α) (a: α) := list.anyP (fun x => a = x)

def List.sorted [Compare α] (list: List α): Prop := match list with
 | [] | [_] => True
 | a :: b :: rest => a <= b ∧ (b::rest).sorted

def List.containsP.pop (as: List α) (a b: α) : as.containsP b -> (a::as).containsP b := by
  intro contains_as
  unfold List.containsP List.anyP
  apply Or.inr
  assumption

def List.sorted.pop [Compare α] (as: List α) (a: α) : (a::as).sorted -> as.sorted := by
  intro aas_sorted
  match as with
  | [] => trivial
  | a'::as' => exact aas_sorted.right