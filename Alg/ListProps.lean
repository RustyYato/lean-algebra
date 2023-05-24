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